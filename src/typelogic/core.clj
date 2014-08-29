(ns typelogic.core
  (:refer-clojure :exclude [== isa? methods])
  (:require [clojure.core :as core]
            [clojure.walk :refer [macroexpand-all] :as walk]
            [clojure.repl :refer [source-fn]]
            [clojure.core.logic :refer :all]
            [clojure.core.logic.pldb :as pldb]
            [typelogic.logic :as logic]
            [typelogic.reflect :as reflect])
  (:import [java.lang.reflect Modifier Method Field Constructor]))

(declare ann)

(defn append [xs x]
  (matcha [xs]
    ([[x . xs']])
    ([[_ . xs']]
       (append xs' x))))

(defna freeze [xs]
  ([[]])
  ([[_ . xs']]
     (freeze xs')))

(defmulti convert
  (fn [type]
    (cond (sequential? type) (first type)
          (class? type) type
          (lvar? type) ::lvar
          (nil? type) ::nil)))

(def box
  {Boolean/TYPE Boolean
   Character/TYPE Character
   Byte/TYPE Byte
   Short/TYPE Short
   Integer/TYPE Integer
   Long/TYPE Long
   Float/TYPE Float
   Double/TYPE Double})

(def upcast
  {::fn clojure.lang.AFunction
   ::seq clojure.lang.ArraySeq
   ::var clojure.lang.Var
   ::lvar Object})

(defmethod convert ::fn [_] clojure.lang.AFunction)
(defmethod convert ::seq [_] clojure.lang.ArraySeq)
(defmethod convert ::var [_] clojure.lang.Var)
(defmethod convert Boolean/TYPE [_] Boolean)
(defmethod convert Character/TYPE [_] Character)
(defmethod convert Byte/TYPE [_] Byte)
(defmethod convert Short/TYPE [_] Short)
(defmethod convert Integer/TYPE [_] Integer)
(defmethod convert Long/TYPE [_] Long)
(defmethod convert Float/TYPE [_] Float)
(defmethod convert Double/TYPE [_] Double)
(defmethod convert ::lvar [_] Object)
(defmethod convert ::nil [_] nil)
(defmethod convert Object [type] type)

(derive ::fn ::any)
(derive ::seq ::any)
(derive ::var ::any)
(derive ::lvar ::any)

(defmulti isa?
  (letfn [(dispatch [type]
            (cond (sequential? type) (first type)
                  (class? type) type
                  (lvar? type) ::lvar))]
    (fn [child parent]
      [(dispatch child) (dispatch parent)])))

(defmethod isa? [::fn ::fn] [[_ params return :as fn] [_ params' return' :as fn']]
  (and (every? #(apply isa? %) (map list params' params))
       (isa? return return')))

(defmethod isa? [::var ::var] [[_ _ type] [_ _ type']]
  (isa? type type'))

(defmethod isa? [::any Object] [[tag & _] class]
  (isa? (upcast tag) class))

(defmethod isa? [Object ::any] [class [tag & _]]
  (isa? class (upcast tag)))

(defmethod isa? :default [child parent]
  (or (nil? child)
      (and (core/isa? (get box child child) Number)
           (core/isa? (get box parent parent) Number))
      (core/isa? child parent)))

#_(defn subtype [sub super]
  (conda
   [(== sub super)]
   [(project [sub super] (== (isa? sub super) true))]
   [(project [sub super] (== (isa? super sub) true))
    (project [sub super] (log "before:" sub))
    (ext-run-csg sub super)
    (project [sub] (log "after:" sub))]))

(defn subtype [sub super]
  (conda
   [(== sub super)]
   [(project [sub super] (== (isa? sub super) true))]
   [(project [sub super] (== (isa? super sub) true))
    (project [sub super] (log "before:" super))
    (ext-run-csg super sub)
    (project [sub] (log "after:" super))]))

(defn ann- [env ctx type expr]
  (fresh [subtype]
    (ann env ctx subtype expr)
    (conda [(== type subtype)]
           [(project [type subtype] (== (isa? subtype type) true))]
           [(project [type subtype] (== (isa? type subtype) true))
            (ext-run-csg type subtype)])))

(defn local [ctx type sym]
  (matcha [ctx]
    ([[[::var sym type] . _]])
    ([[_ . ctx']]
      (nonlvaro ctx')
      (local ctx' type sym))))

(defn global [env ctx type symbol]
  (binding [*ns* (::ns ctx)]
    (if-let [var (resolve symbol)]
      (if (class? var)
        (== type Class)
        (if-let [expr (source-fn symbol)]
          (ann env {::ns (:ns (meta var))} type (read-string expr))
          (throw (RuntimeException. "Source not found"))))
      (throw (RuntimeException. (str "Unable to resolve symbol: " symbol " in this context"))))))

(defmulti ann-app
  (fn [env ctx type & exprs]
    (first exprs)))

(defmethod ann-app 'if
  ([env ctx type tag]
     (throw (RuntimeException. "Too few arguments to if")))
  ([env ctx type tag test]
     (ann-app env ctx type tag))
  ([env ctx type tag test then]
     (ann-app env ctx type tag test then nil))
  ([env ctx type tag test then else]
     (all
       (fresh [type] (ann env ctx type test))
       (ann- env ctx type then)
       (ann- env ctx type else)))
  ([env ctx type tag test then else & args]
     (throw (RuntimeException. "Too many arguments to if"))))

(defmethod ann-app 'do [env ctx type tag & [expr & exprs' :as exprs]]
  (cond (empty? exprs) (== type nil)
        (empty? exprs') (ann env ctx type expr)
        :else (all
                (fresh [type] (ann env ctx type expr))
                (apply ann-app env ctx type tag exprs'))))

(defn ann-tag [type sym]
  (all
    (pred sym symbol?)
    (is type sym reflect/tag)
    (pred type (complement nil?))))

(defmethod ann-app 'let* [env ctx type tag [var expr & bindings' :as bindings] & exprs]
  (if (empty? bindings)
    (apply ann-app env ctx type 'do exprs)
    (fresh [val]
      (conda [(ann-tag val var)]
             [(ann env ctx val expr)])
      (apply ann-app env (assoc ctx var val) type tag bindings' exprs))))

(defmethod ann-app 'loop* [env ctx type tag bindings & exprs]
  (let [bindings (partition 2 bindings)]
    (ann env ctx type `((fn* (~(vec (map first bindings)) ~@exprs)) ~@(map second bindings)))))

(defn ann-fn [env ctx return params [sym & syms' :as syms] body]
  (cond (empty? syms) (all
                        (emptyo params)
                        (apply ann-app env (assoc ctx 'recur [::fn params return]) return 'do body))
        (= sym '&) (fresh [param]
                     (== params [[::seq]])
                     (apply ann-app env (assoc ctx (first syms') param) return 'do body))
        :else (fresh [param params']
                (conso param params' params)
                (if-let [tag (reflect/tag sym)]
                  (== param tag)
                  succeed)
                (ann-fn env (assoc ctx sym param) return params' syms' body))))

(defn ann-fns [env ctx return params [syms & body] & exprs]
  (conde [(ann-fn env ctx return params syms body)]
         [(if (empty? exprs)
            fail
            (apply ann-fns env ctx return params exprs))]))

(defmethod ann-app 'fn* [env ctx type tag expr & exprs]
  (if (symbol? expr)
    (fresh [type']
      (apply ann-app env (assoc ctx expr type') type tag exprs)
      (fresh [type]
        (apply ann-app env (assoc ctx expr type) type' tag exprs)))
    (fresh [params return]
      (== type [::fn params return])
      (cond (seq? expr) (apply ann-fns env ctx return params expr exprs)
            (vector? expr) (ann-fn env ctx return params expr exprs)))))

(defmethod ann-app 'def
  ([env ctx type tag name]
     (matcha [type] ([[::var name _]])))
  ([env ctx type tag name expr]
     (let [macro? (:macro (meta name))]
       (if macro?
         fail
         (fresh [type' self]
           (== type [::var name type'])
           (ann env (assoc ctx name self) type' expr)
           (fresh [type] (ann env (assoc ctx name type) self expr))
           (append env type))))))

(defmethod ann-app 'quote [env ctx type tag & exprs]
  (== type (class (first exprs))))

(defn app [env ctx params [arg & args' :as args]]
  (if (empty? args)
    (matcha [params]
      ([[]])
      ([[[:seq]]]))
    (conda [(pred params #(= % [:seq]))
            (fresh [type] (ann env ctx type arg))
            (app env ctx params args')]
           [(fresh [param params']
              (conso param params' params)
              #_(ext-run-csg params (lcons param params'))
              (ann- env ctx param arg)
              (app env ctx params' args'))])))

(defmethod ann-app 'new [env ctx type tag name & args]
  (let [class (resolve name)]
    (if (class? class)
      (fresh [params]
        (logic/any params (reflect/constructors class))
        (app env ctx params args)
        (== type class))
      (throw (IllegalArgumentException. (str "Unable to resolve classname: " name))))))

(defmethod ann-app '. [env ctx type tag obj msg & args]
  (if (seq? msg)
    (apply ann-app env ctx type tag obj msg)
    (fresh [class]
      (or (if (symbol? obj)
            (let [var (resolve obj)]
              (if (class? var)
                (== class var))))
          (fresh [type]
            (ann env ctx type obj)
            (is class type convert)))
      (project [class]
        (conda [(fresh [params]
                  (logic/any [params type] (reflect/methods class msg))
                  (app env ctx params args))]
               #_[(all
                  (is type class #(reflect/field % msg))
                  (pred type class?))])))))

(defmethod ann-app 'throw [env ctx type tag e]
  (ann env ctx Throwable e))

(defn ifn->fn [ifn fn]
  (conda [(matcha [ifn]
            ([[::fn _ _]] (== fn ifn))
            ([[::var _ fn]]))]
         [(pred ifn #(isa? % clojure.lang.IFn))
          (matcha [fn] ([[::fn _ _]]))]))

(defmethod ann-app :default [env ctx type f & args]
  (fresh [ifn fn params]
    (ann env ctx fn f)
    #_(trace-s)
    (ifn->fn ifn fn)
    (ext-run-csg fn [::fn params type])
    (app env ctx params args)))

(defmethod ann-app nil [env ctx type]
  (== type clojure.lang.PersistentList$EmptyList))

(defn ann [env ctx type expr]
  (let [expr (macroexpand expr)]
    (cond (symbol? expr) (conda [(pred ctx #(contains? % expr))
                                 (ext-run-csg type (ctx expr))]
                                [(global env ctx type expr)])
          (seq? expr) (apply ann-app env ctx type expr)
          :else (== type (class expr)))))

(defn check
  ([expr]
     (check {} expr))
  ([ctx expr]
     (distinct
      (run* [q]
        (fresh [env type]
          (== q [env type])
          (ann env (assoc ctx ::ns *ns*) type expr)
          (freeze env))))))

(defn read-env [expr]
  (let [vars (atom {})]
    (walk/prewalk
      (fn [expr]
        (if (and (symbol? expr) (re-matches #"_\d+" (name expr)))
          (if-let [var (@vars expr)]
            var
            (let [var (lvar)]
              (swap! vars assoc expr var)
              var))
          expr))
      expr)))

(defn check-all [& exprs]
  (loop [ctx []
         [expr & exprs' :as exprs] exprs
         types []]
    (if-not (empty? exprs)
      (let [[env type] (check ctx expr)]
        (recur (concat (read-env env) ctx) exprs' (cons type types))))))

(check '(defn f [a] (if true 0 (f ""))))
