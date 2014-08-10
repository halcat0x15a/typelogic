(ns typelogic.core
  (:refer-clojure :exclude [== isa? methods])
  (:require [clojure.core :as core]
            [clojure.walk :refer [macroexpand-all]]
            [clojure.repl :refer [source-fn]]
            [clojure.core.logic :refer :all]
            [clojure.core.logic.pldb :as pldb])
  (:import [java.lang.reflect Modifier Method Field Constructor]))

(declare ann)

(defmulti convert
  (fn [type]
    (cond (sequential? type) (first type)
          (class? type) type)))

(defmethod convert :fn [_] clojure.lang.AFunction)
(defmethod convert :seq [_] clojure.lang.ArraySeq)
(defmethod convert :var [_] clojure.lang.Var)
(defmethod convert :overloaded [_] clojure.lang.AFunction)
(defmethod convert Boolean/TYPE [_] Boolean)
(defmethod convert Character/TYPE [_] Character)
(defmethod convert Byte/TYPE [_] Byte)
(defmethod convert Short/TYPE [_] Short)
(defmethod convert Integer/TYPE [_] Integer)
(defmethod convert Long/TYPE [_] Long)
(defmethod convert Float/TYPE [_] Float)
(defmethod convert Double/TYPE [_] Double)
(defmethod convert nil [_] Object)
(defmethod convert :default [type] type)

(defn isa? [a b]
  (or (and (nil? a) (core/isa? b Object))
      (and (core/isa? a Number) (core/isa? b Number))
      (core/isa? a b)))

(defn <:< [sub super]
  (fn [cont]
    (conda
     [(== sub super)
      cont]
     [(project [sub]
        (letfn [(pred [type] (isa? (convert sub) (convert type)))
                (form [_ _ r s] (list sub '<:< (-reify s super r)))]
          (predc super pred form)))
      cont])))

(defn <:<' [sub super]
  (matche [super]
    ([[:overloaded fn . fns]]
       (conda [(<:< sub fn)]
              [(<:<' sub (lcons :overloaded fns))]))
    ([[:var _ type]]
       (<:< sub type))
    ([_] (<:< sub super))))

(defn ann' [ns env ctx type expr]
  (fn [cont]
    (fresh [sub]
      ((ann ns env ctx sub expr)
       ((<:< sub type)
        cont)))))

(defn local [ctx type sym]
  (matcha [ctx]
    ([[[sym type] . _]])
    ([[_ . ctx']]
       (local ctx' type sym))))

(defn global [ns env type symbol]
  (fn [cont]
    (binding [*ns* ns]
      (if-let [var (resolve symbol)]
        (if (class? var)
          (== type Class)
          ((some->> symbol source-fn read-string (ann' (:ns (meta var)) env [] type)) cont))
        (throw (RuntimeException. (str "Unable to resolve symbol: " symbol " in this context")))))))

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
     (fn [cont]
       (all
         (fresh [type']
           ((ann ns env ctx type test)
            ((ann' ns env ctx type then)
             ((ann' ns env ctx type else)
              cont)))))))
  ([ns env ctx type tag test then else & args]
     (throw (RuntimeException. "Too many arguments to if"))))

(defmethod special 'do [ns env ctx type tag & [expr & exprs' :as exprs]]
  (fn [cont]
    (cond (empty? exprs) (all (== type nil) cont)
          (empty? exprs') ((ann ns env ctx type expr) cont)
          :else (fresh [type']
                  ((ann ns env ctx type expr)
                   ((apply special ns env ctx type tag exprs')
                    cont))))))

(defmethod special 'let* [ns env ctx type tag [var expr & bindings' :as bindings] & exprs]
  (fn [cont]
    (if (empty? bindings)
      ((apply special ns env ctx type 'do exprs) cont)
      (fresh [val]
        ((ann ns env ctx val expr)
         ((apply special ns env (lcons [var val] ctx) type tag bindings' exprs)
          cont))))))

(def primitives
  {'long Long/TYPE
   'double Double/TYPE})

(defn tag [sym]
  (if-let [tag (some-> sym meta :tag)]
    (if-let [class (primitives tag)]
      class
      (if-let [var (resolve tag)]
        (if (class? var)
          var)))))

(defna bind [syms params bindings]
  ([[] [] []])
  ([['& sym] [[:seq]] [[sym [:seq]]]])
  ([[sym . syms'] [param . params'] [[sym param] . bindings']]
     (conda [(all
               (is param sym tag)
               (pred param (complement nil?)))]
            [succeed])
     (bind syms' params' bindings')))

(defn ann-fn [ns env ctx type syms & exprs]
  (fn [cont]
    (fresh [params return bindings ctx']
      (== type [:fn params return])
      (bind syms params bindings)
      (appendo (lcons ['recur type] bindings) ctx ctx')
      ((apply special ns env ctx' return 'do exprs) cont))))

(defn ann-overloaded [ns env ctx fns [[syms & body] & exprs' :as exprs]]
  (fn [cont]
    (if (empty? exprs)
      (all (== fns []) cont)
      (fresh [fn fns' ctx']
        (conso fn fns' fns)
        ((ann-fn ns env ctx fn syms body)
         ((ann-overloaded ns env ctx fns' exprs')
          cont))))))

(defmethod special 'fn*
  ([ns env ctx type tag]
     (fn [cont] fail))
  ([ns env ctx type tag expr & exprs]
     (prn ns env ctx type tag expr exprs)
     (fn [cont]
       (cond (seq? expr) (conde [((apply ann-fn ns env ctx type expr) cont)]
                                [((apply special ns env ctx type tag exprs) cont)])
             (vector? expr) ((apply ann-fn ns env ctx type expr exprs) cont)
             (symbol? expr) (fresh [type']
                              ((apply special ns env (lcons [expr type'] ctx) type tag exprs) cont))))))

(defmethod special 'def
  ([ns env ctx type tag name]
     (fn [cont]
       (all
         (== type [:var name])
         cont)))
  ([ns env ctx type tag name expr]
     (fn [cont]
       (fresh [type' self]
         (== type [:var name type'])
         ((ann ns env (lcons [name self] ctx) type' expr) cont)))))

(defmethod special 'quote [ns env ctx type tag & exprs]
  (fn [cont]
    (all (== type (class (first exprs)) cont))))

(defne ->fn [type fn]
  ([[:fn . _] type])
  ([[:var _ type'] _]
     (pred type' (complement lvar?))
     (->fn type' fn))
  ([[:overloaded . fns] _]
     (matche [fns]
       ([[fn . _]])
       ([[_ . fns']]
          (->fn (lcons :overloaded fns') fn)))))

(defn ann-params [ns env ctx params [arg & args' :as args]]
  (fn [cont]
    (if (empty? args)
      (== params [])
      (fresh [param params']
        (conso param params' params)
        (conde [(all (pred param #(= % [:seq])) cont)]
               [(ann' ns env ctx param arg)
                ((ann-params ns env ctx params' args') cont)])))))

(defn app [ns env ctx type f args]
  (fn [cont]
    (fresh [params]
      (conde [(all
                (->fn f [:fn params type])
                ((ann-params ns env ctx params args) cont))]
             [(pred f #(isa? % clojure.lang.IFn))
              cont]))))

(defn constructors [^Class class]
  (->> (.getConstructors class)
       (map #(vector :fn (seq (.getParameterTypes ^Constructor %)) class))
       (cons :overloaded)))

(defmethod special 'new [ns env ctx type tag name & args]
  (fn [cont]
    (let [class (resolve name)]
      (if (class? class)
        ((app ns env ctx type (constructors class) args) cont)
        (throw (IllegalArgumentException. (str "Unable to resolve classname: " name)))))))

(defn field [^Class class field]
  (try
    (.getField class (name field))
    (catch NoSuchFieldException _)))

(defn ann-field [type class field]
  (all
    (is type class #(field % field))
    (pred type class?)))

(defn methods [^Class class method]
  (->> (.getMethods class)
       (filter #(= (.getName ^Method %) (name method)))
       (map (fn [^Method m] [:fn (vec (.getParameterTypes m)) (.getReturnType m)]))
       (cons :overloaded)))

(defn ann-method [ns env ctx type class name & args]
  (fn [cont]
    (project [class]
      ((app ns env ctx type (methods class name) args) cont))))

(defmethod special '. [ns env ctx type tag obj msg & args]
  (fn [cont]
    (fresh [class]
      (or (if (symbol? obj)
            (let [var (resolve obj)]
              (if (class? var)
                (== class var))))
          (fresh [type]
            (ann ns env ctx type obj)
            (is class type convert))
          fail)
      (cond (seq? msg) (apply ann-method ns env ctx type class msg)
            (symbol? msg) (conda [(ann-field type class msg)]
                                 [(apply ann-method ns env ctx type class msg args)])))))

(defmethod special 'throw [ns env ctx type tag e]
  (fn [cont]
    ((ann' ns env ctx Throwable e) cont)))

(defmethod special :default [ns env ctx type f & args]
  (fn [cont]
    (fresh [fn]
      ((ann ns env ctx fn f)
       ((app ns env ctx type fn args)
        cont)))))

(defmethod special nil [ns env ctx type]
  (fn [cont]
    (all (== type clojure.lang.PersistentList$EmptyList) cont)))

(defn ann [ns env ctx type expr]
  (fn [cont]
    (let [expr (macroexpand expr)]
      (cond (symbol? expr) (conda [(all (local ctx type expr) cont)]
                                  [((global ns env type expr) cont)])
            (seq? expr) ((apply special ns env ctx type expr) cont)
            :else (all (== type (class expr)) cont)))))

(defn check [expr]
  (doall
   (run* [q]
     (fresh [env type]
       (== q [env type])
       ((ann *ns* env [] type expr) succeed)))))


(check '((fn ([a] a) ([a b] b)) 0))
