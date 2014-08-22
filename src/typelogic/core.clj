(ns typelogic.core
  (:refer-clojure :exclude [== isa? methods])
  (:require [clojure.core :as core]
            [clojure.walk :refer [macroexpand-all] :as walk]
            [clojure.repl :refer [source-fn]]
            [clojure.core.logic :refer :all]
            [clojure.core.logic.pldb :as pldb]
            [typelogic.logic :as logic])
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

(defmethod convert :fn [_] clojure.lang.AFunction)
(defmethod convert :seq [_] clojure.lang.ArraySeq)
(defmethod convert :var [_] clojure.lang.Var)
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

(defn isa? [child parent]
  (let [child (convert child)
        parent (convert parent)]
    (or (and (nil? child) (core/isa? parent Object))
        (and (core/isa? child Number) (core/isa? parent Number))
        (core/isa? child parent))))

(defn isa [sub super]
  (conda
   [(== sub super)]
   [(project [sub super] (== (isa? sub super) true))
    (ext-run-csg super sub)]))

(defn has [sub super]
  (matcha [sub super]
    ([[:fn [params return]] [:fn [params' return'] . _]]
       (logic/map isa params params')
       (isa return return'))
    ([_ [:fn _ . types]]
       (nonlvaro types)
       (has sub (lcons :fn types)))
    ([_ sub])))

(defn type-tag [type sym]
  (all
    (pred sym symbol?)
    (or (if-let [tag (some-> sym meta :tag)]
          (if-let [class (primitives tag)]
            (== type class)
            (if-let [var (resolve tag)]
              (if (class? var)
                (== type var)))))
        fail)))

(defn ann' [ns env ctx type expr]
  (fresh [sub]
    (ann ns env ctx sub expr)
    (isa sub type)))

(defn local [ctx type sym]
  (matcha [ctx]
    ([[[:var sym type] . _]])
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
       (ann' ns env ctx type then)
       (ann' ns env ctx type else)))
  ([ns env ctx type tag test then else & args]
     (throw (RuntimeException. "Too many arguments to if"))))

(defmethod special 'do [ns env ctx type tag & [expr & exprs' :as exprs]]
  (cond (empty? exprs) (== type nil)
        (empty? exprs') (ann ns env ctx type expr)
        :else (all
                (fresh [type] (ann ns env ctx type expr))
                (apply special ns env ctx type tag exprs'))))

(defmethod special 'let* [ns env ctx type tag [var expr & bindings' :as bindings] & exprs]
  (if (empty? bindings)
    (apply special ns env ctx type 'do exprs)
    (fresh [val]
      (conda [(type-tag val var)]
             [(ann ns env ctx val expr)])
      (apply special ns env (lcons [:var var val] ctx) type tag bindings' exprs))))

(defmethod special 'loop* [ns env ctx type tag bindings & exprs]
  (let [bindings (partition 2 bindings)]
    (ann ns env ctx type `((fn* (~(vec (map first bindings)) ~@exprs)) ~@(map second bindings)))))

(defna bind [syms params bindings]
  ([[] [] []])
  ([['& sym] [[:seq]] [[:var sym [:seq]]]])
  ([[sym . syms'] [param . params'] [[:var sym param] . bindings']]
     (conda [(project [sym] (type-tag param sym))]
            [succeed])
     (bind syms' params' bindings')))

(defn ann-fn [ns env ctx types [[syms & body] & exprs' :as exprs]]
  (if (empty? exprs)
    (== types [])
    (fresh [params return types' ctx' bindings]
      (conso [params return] types' types)
      (bind syms params bindings)
      (appendo (lcons [:var 'recur [:fn [params return]]] bindings) ctx ctx')
      (apply special ns env ctx' return 'do body)
      (ann-fn ns env ctx types' exprs'))))

(defmethod special 'fn*
  ([ns env ctx type tag] fail)
  ([ns env ctx type tag expr & exprs]
     (cond (seq? expr) (fresh [types]
                         (conso :fn types type)
                         (ann-fn ns env ctx types (cons expr exprs)))
           (vector? expr) (special ns env ctx type tag (cons expr exprs))
           (symbol? expr) (fresh [type']
                            (apply special ns env (lcons [:var expr type'] ctx) type tag exprs)
                            (has type' type)))))

(defmethod special 'def
  ([ns env ctx type tag name]
     (matcha [type] ([[:var name _]])))
  ([ns env ctx type tag name expr]
     (let [macro? (:macro (meta name))]
       (if macro?
         fail
         (fresh [type' self]
           (== type [:var name type'])
           (ann ns env (lcons [:var name self] ctx) type' expr)
           (has self type')
           (append env type))))))

(defmethod special 'quote [ns env ctx type tag & exprs]
  (== type (class (first exprs))))

(defn ann-list [ns env ctx params [arg & args' :as args]]
  (if (empty? args)
    (== params [])
    (fresh [param params']
      (conso param params' params)
      (conda [(pred param #(= % [:seq]))]
             [(ann' ns env ctx param arg)
              (ann-list ns env ctx params' args')]))))

(defn app [ns env ctx type f args]
  (matche [f]
    ([[:fn [params type] . types]]
      (ann-list ns env ctx params args))
    ([[:fn _ . types]]
      (nonlvaro types)
      (app ns env ctx type (lcons :fn types) args))))

(defn constructors [^Class class]
  (->> (.getConstructors class)
       (map #(vector (vec (.getParameterTypes ^Constructor %)) class))
       (cons :fn)))

(defmethod special 'new [ns env ctx type tag name & args]
  (let [class (resolve name)]
    (if (class? class)
      (app ns env ctx type (constructors class) args)
      (throw (IllegalArgumentException. (str "Unable to resolve classname: " name))))))

(defn field [^Class class field]
  (try
    (.. class (getField (name field)) (getType))
    (catch NoSuchFieldException _)))

(defn methods [^Class class method]
  (->> (.getMethods class)
       (filter #(= (.getName ^Method %) (name method)))
       (map (fn [^Method m] [(vec (.getParameterTypes m)) (.getReturnType m)]))
       (cons :fn)))

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
                  (is type class #(field % msg))
                  (pred type class?))]
               [(app ns env ctx type (methods class msg) args)])))))

(defmethod special 'throw [ns env ctx type tag e]
  (ann' ns env ctx Throwable e))

(defn ifn->fn [ifn fn]
  (conda [(matcha [ifn]
            ([[:fn _ . rest]]
               (conda [(== rest [])] [succeed])
               (== fn ifn))
            ([[:var _ fn]]))]
         [(pred ifn #(isa? % clojure.lang.IFn))
          (matcha [fn] ([[:fn [_ _]]]))]))

(defmethod special :default [ns env ctx type f & args]
  (fresh [ifn fn]
    (ann ns env ctx ifn f)
    (ifn->fn ifn fn)
    (app ns env ctx type fn args)))

(defmethod special nil [ns env ctx type]
  (== type clojure.lang.PersistentList$EmptyList))

(defn ann [ns env ctx type expr]
  (let [expr (macroexpand expr)]
    (cond (symbol? expr) (conda [(membero [:var expr type] ctx)]
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
