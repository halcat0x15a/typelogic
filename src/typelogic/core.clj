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

(def box
  {Boolean/TYPE Boolean
   Character/TYPE Character
   Byte/TYPE Byte
   Short/TYPE Short
   Integer/TYPE Integer
   Long/TYPE Long
   Float/TYPE Float
   Double/TYPE Double})

(defmulti convert
  (fn [type]
    (cond (sequential? type) (first type)
          (class? type) type
          (lvar? type) ::lvar)))

(defmethod convert ::fn [_] clojure.lang.AFunction)
(defmethod convert ::seq [_] clojure.lang.ArraySeq)
(defmethod convert ::var [_] clojure.lang.Var)
(defmethod convert ::lvar [_] Object)
(defmethod convert :default [type] type)

(defn isa? [child parent]
  (or (nil? child)
      (and (core/isa? (get box child child) Number)
           (core/isa? (get box parent parent) Number))
      (core/isa? (convert child) (convert parent))))

(declare subtype)

(defna subtypes [subs supers]
  ([[] []])
  ([[sub . subs'] [super . supers']]
     (subtype sub super)
     (subtypes subs' supers')))

(defna subfn [sub super]
  ([[::fn [params type] . types] [::fn [params' type'] . types']]
    (conda [(all
              (subtype type type')
              (subtypes params' params))]
           [(subfn sub [::fn types'])]
           [(subfn [::fn types] super)])))

(defna subvar [sub super]
  ([[::var _ type] [::var _ type']]
    (subtype type type')))

(defn subtype [sub super]
  (conda [(== sub super)]
         [(subfn sub super)]
         [(subvar sub super)]
         [(project [super sub] (== (isa? sub super) true))]
         [(project [super sub] (== (isa? super sub) true))
          (ext-run-csg super sub)]))

(defn ann- [env ctx type expr]
  (fresh [sub]
    (ann env ctx sub expr)
    (subtype sub type)))

(defn global [env ctx type symbol]
  (binding [*ns* (::ns ctx)]
    (if-let [var (resolve symbol)]
      (if (class? var)
        (== type Class)
        (if-let [expr (source-fn symbol)]
          (ann env {::ns (:ns (meta var))} type (read-string expr))
          (throw (ex-info "Source not found" {:symbol symbol}))))
      (throw (RuntimeException. (str "Unable to resolve symbol: " symbol " in this context"))))))

(defmulti ann-app
  (fn [env ctx type & exprs]
    (first exprs)))

(defmethod ann-app 'if
  ([env ctx type tag]
     (throw (ex-info "Too few arguments to if" {})))
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
     (throw (ex-info "Too many arguments to if" {}))))

(defmethod ann-app 'do [env ctx type tag & [expr & exprs' :as exprs]]
  (cond (empty? exprs) (== type nil)
        (empty? exprs') (ann env ctx type expr)
        :else (all
                (fresh [type] (ann env ctx type expr))
                (apply ann-app env ctx type tag exprs'))))

(defn ann-tag [type sym]
  (if-let [tag (reflect/tag sym)]
    (== type tag)
    succeed))

(defmethod ann-app 'let* [env ctx type tag [var expr & bindings' :as bindings] & exprs]
  (if (empty? bindings)
    (apply ann-app env ctx type 'do exprs)
    (fresh [val]
      (ann-tag val var)
      (ann- env ctx val expr)
      (apply ann-app env (assoc ctx var val) type tag bindings' exprs))))

(defn ann-fn [env ctx return params [sym & syms' :as syms] body]
  (cond (empty? syms) (all
                        (emptyo params)
                        (apply ann-app env ctx return 'do body))
        (= sym '&) (fresh [param]
                     (== params [[::seq]])
                     (apply ann-app env (assoc ctx (first syms') param) return 'do body))
        :else (fresh [param params']
                (conso param params' params)
                (ext-run-csg params (lcons param params'))
                (ann-tag param sym)
                (ann-fn env (assoc ctx sym param) return params' syms' body))))

(defn ann-fns [env ctx types [[syms & body] & exprs' :as exprs]]
  (if (empty? exprs)
    (emptyo types)
    (fresh [params return types']
      (conso [params return] types' types)
      (ann-fn env (assoc ctx ::recur [params return]) return params syms body)
      (ann-fns env ctx types' exprs'))))

(defmethod ann-app 'fn* [env ctx type tag expr & exprs]
  (if (symbol? expr)
    (fresh [type']
      (apply ann-app env (assoc ctx expr type') type tag exprs)
      (subtype type' type))
    (fresh [types]
      (conso ::fn types type)
      (cond (seq? expr) (ann-fns env ctx types (cons expr exprs))
            (vector? expr) (ann-fns env ctx types (list (cons expr exprs)))))))

(defmethod ann-app 'loop* [env ctx type tag bindings & exprs]
  (let [bindings (partition 2 bindings)]
    (ann env ctx type `((fn* (~(vec (map first bindings)) ~@exprs)) ~@(map second bindings)))))

(defn app [env ctx params [arg & args' :as args]]
  (if (empty? args)
    (matcha [params]
      ([[]])
      ([[[:seq]]]))
    (conda [(pred params #(= % [[:seq]]))
            (fresh [type] (ann env ctx type arg))
            (app env ctx params args')]
           [(fresh [param params']
              (conso param params' params)
              (ext-run-csg params (lcons param params'))
              (ann- env ctx param arg)
              (app env ctx params' args'))])))

(defmethod ann-app 'recur [env ctx type tag & args]
  (let [[params return] (::recur ctx)]
    (all
      (== type return)
      (app env ctx params args))))

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
           (subtype self type')
           (conda [(== self type')] [succeed])
           (append env type))))))

(defmethod ann-app 'quote [env ctx type tag & exprs]
  (== type (class (first exprs))))

(defn apps [env ctx return types args]
  (fresh [params types']
    (conso [params return] types' types)
    (ext-run-csg types (lcons [params return] types'))
    (conde [(app env ctx params args)]
           [(apps env ctx return types' args)]
           #_[(project [types] (throw (ex-info "type mismatch;" {:op [::fn (seq types)] :args args})))])))

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
        (conda [(apps env ctx type (reflect/methods class msg) args)]
               #_[(all
                  (is type class #(reflect/field % msg))
                  (pred type class?))])))))

(defmethod ann-app 'throw [env ctx type tag e]
  (ann env ctx Throwable e))

(defn ifn->fn [ifn fn]
  (conda [(matcha [ifn]
            ([[::fn . _]] (ext-run-csg fn ifn))
            ([[::var _ fn]]))]
         [(pred ifn #(isa? % clojure.lang.IFn))
          (matcha [fn] ([[::fn . _]]))]))

(defmethod ann-app :default [env ctx type f & args]
  (fresh [ifn fn types]
    (ann env ctx ifn f)
    (ifn->fn ifn fn)
    (conso ::fn types fn)
    (ext-run-csg fn (lcons ::fn types))
    (apps env ctx type types args)))

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
     (first
      (run* [q]
        (fresh [env type]
          (== q [env type])
          (condu [(ann env (assoc ctx ::ns *ns*) type expr)])
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
