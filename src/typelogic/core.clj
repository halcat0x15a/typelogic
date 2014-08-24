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

(defn subtype [sub super]
  (conda
   [(== sub super)]
   [(project [sub super] (== (isa? sub super) true))]
   [(project [sub super] (== (isa? super sub) true))
    (project [sub super] (log "before:" sub))
    (ext-run-csg sub super)
    (project [sub] (log "after:" sub))]))

(defn local [ctx type sym]
  (matcha [ctx]
    ([[[::var sym type] . _]])
    ([[_ . ctx']]
      (nonlvaro ctx')
      (local ctx' type sym))))

(defn global [ns env type symbol]
  (binding [*ns* ns]
    (if-let [var (resolve symbol)]
      (if (class? var)
        (== type Class)
        (if-let [expr (source-fn symbol)]
          (ann (:ns (meta var)) env [] type (read-string expr))
          (throw (RuntimeException. "Source not found"))))
      (throw (RuntimeException. (str "Unable to resolve symbol: " symbol " in this context"))))))

(defmulti special
  (fn [ns env ctx type & exprs]
    (first exprs)))

(defmethod special 'if
  ([ns env ctx type tag]
     (throw (RuntimeException. "Too few arguments to if")))
  ([ns env ctx type tag test]
     (special ns env ctx type tag))
  ([ns env ctx type tag test then]
     (special ns env ctx type tag test then nil))
  ([ns env ctx type tag test then else]
     (all
       (fresh [type] (ann ns env ctx type test))
       (ann ns env ctx type then)
       (ann ns env ctx type else)))
  ([ns env ctx type tag test then else & args]
     (throw (RuntimeException. "Too many arguments to if"))))

(defmethod special 'do [ns env ctx type tag & [expr & exprs' :as exprs]]
  (cond (empty? exprs) (== type nil)
        (empty? exprs') (ann ns env ctx type expr)
        :else (all
                (fresh [type] (ann ns env ctx type expr))
                (apply special ns env ctx type tag exprs'))))

(defn ann-tag [type sym]
  (all
    (pred sym symbol?)
    (is type sym reflect/tag)
    (pred type (complement nil?))))

(defmethod special 'let* [ns env ctx type tag [var expr & bindings' :as bindings] & exprs]
  (if (empty? bindings)
    (apply special ns env ctx type 'do exprs)
    (fresh [val]
      (conda [(ann-tag val var)]
             [(ann ns env ctx val expr)])
      (apply special ns env (lcons [::var var val] ctx) type tag bindings' exprs))))

(defmethod special 'loop* [ns env ctx type tag bindings & exprs]
  (let [bindings (partition 2 bindings)]
    (ann ns env ctx type `((fn* (~(vec (map first bindings)) ~@exprs)) ~@(map second bindings)))))

(defna bind [syms params bindings]
  ([[] [] []])
  ([['& sym] [[::seq]] [[::var sym [::seq]]]])
  ([[sym . syms'] [param . params'] [[::var sym param] . bindings']]
     (conda [(ann-tag param sym)]
            [succeed])
     (bind syms' params' bindings')))

(defn ann-fn [ns env ctx type syms body]
  (fresh [params return bindings ctx']
    (== [::fn params return] type)
    (bind syms params bindings)
    (appendo (lcons [::var 'recur type] bindings) ctx ctx')
    (apply special ns env ctx' return 'do body)))

(defmethod special 'fn*
  ([ns env ctx type tag] fail)
  ([ns env ctx type tag expr & exprs]
     (cond (seq? expr) (fresh [syms body]
                         (logic/any (lcons syms body) (cons expr exprs))
                         (project [body] (ann-fn ns env ctx type syms body)))
           (vector? expr) (special ns env ctx type tag expr exprs)
           (symbol? expr) (fresh [type']
                            (apply special ns env (lcons [::var expr type'] ctx) type tag exprs)
                            (fresh [type] (apply special ns env (lcons [::var expr type] ctx) type' tag exprs))))))

(defmethod special 'def
  ([ns env ctx type tag name]
     (matcha [type] ([[::var name _]])))
  ([ns env ctx type tag name expr]
     (let [macro? (:macro (meta name))]
       (if macro?
         fail
         (fresh [type' self]
           (== type [::var name type'])
           (ann ns env (lcons [::var name self] ctx) type' expr)
           (fresh [type] (ann ns env (lcons [::var name type] ctx) self expr))
           (append env type))))))

(defmethod special 'quote [ns env ctx type tag & exprs]
  (== type (class (first exprs))))

(defn app [ns env ctx params [arg & args' :as args]]
  (if (empty? args)
    (matcha [params]
      ([[]])
      ([[[:seq]]]))
    (matcha [params]
      ([[[:seq]]]
        (fresh [type] (ann ns env ctx type arg))
        (app ns env ctx params args'))
      ([[param . params']]
        (fresh [type]
          (ann ns env ctx type arg)
          (subtype type param))
        (app ns env ctx params' args')))))

(defmethod special 'new [ns env ctx type tag name & args]
  (let [class (resolve name)]
    (if (class? class)
      (fresh [params]
        (logic/any params (reflect/constructors class))
        (app ns env ctx params args)
        (== type class))
      (throw (IllegalArgumentException. (str "Unable to resolve classname: " name))))))

(defmethod special '. [ns env ctx type tag obj msg & args]
  (if (seq? msg)
    (apply special ns env ctx type tag obj msg)
    (fresh [class]
      (or (if (symbol? obj)
            (let [var (resolve obj)]
              (if (class? var)
                (== class var))))
          (fresh [type]
            (ann ns env ctx type obj)
            (is class type convert)))
      (project [class]
        (conda [(all
                  (is type class #(reflect/field % msg))
                  (pred type class?))]
               [(fresh [params]
                  (logic/any [params type] (reflect/methods class msg))
                  (app ns env ctx params args))])))))

(defmethod special 'throw [ns env ctx type tag e]
  (ann ns env ctx Throwable e))

(defn ifn->fn [ifn fn]
  (conda [(matcha [ifn]
            ([[::fn _ _]] (== fn ifn))
            ([[::var _ fn]]))]
         [(pred ifn #(isa? % clojure.lang.IFn))
          (matcha [fn] ([[::fn _ _]]))]))

(defmethod special :default [ns env ctx type f & args]
  (fresh [ifn params]
    (ann ns env ctx ifn f)
    (ifn->fn ifn [::fn params type])
    (app ns env ctx params args)))

(defmethod special nil [ns env ctx type]
  (== type clojure.lang.PersistentList$EmptyList))

(defn ann [ns env ctx type expr]
  (let [expr (macroexpand expr)]
    (cond (symbol? expr) (conda [(membero [::var expr type] ctx)]
                                [(global ns env type expr)])
          (seq? expr) (apply special ns env ctx type expr)
          :else (== type (class expr)))))

(defn check
  ([expr]
     (check [] expr))
  ([ctx expr]
     (distinct
      (run* [q]
        (fresh [env types]
          (== q [env types])
          (ann *ns* env ctx types expr)
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
