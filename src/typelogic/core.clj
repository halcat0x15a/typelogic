(ns typelogic.new
  (:refer-clojure :exclude [== isa?])
  (:require [clojure.core :as core]
            [clojure.walk :refer [macroexpand-all]]
            [clojure.repl :refer [source-fn]]
            [clojure.core.logic :refer :all]
            [clojure.core.logic.pldb :as pldb]
            [typelogic.reflect :as reflect]))

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
  (conde
   [(== sub super)]
   [(project [sub]
      (letfn [(pred [type] (isa? (convert sub) (convert type)))
              (form [_ _ r s] (list sub '<:< (-reify s super r)))]
        (predc super pred form)))]))

(defn <:<' [sub super]
  (matche [super]
    ([[:overloaded fn . fns]]
       (conda [(<:< sub fn)]
              [(<:<' sub (lcons :overloaded fns))]))
    ([[:var _ type]]
       (<:< sub type))
    ([_] (<:< sub super))))

(defn ann' [ctx type expr]
  (fresh [sub]
    (ann ctx sub expr)
    (<:< sub type)))

(defn local [ctx type sym]
  (matcha [ctx]
    ([[[sym type] . _]])
    ([[_ . ctx']]
       (local ctx' type sym))))

(defn global [type symbol]
  (if-let [var (resolve symbol)]
    (if (class? var)
      (== type Class)
      (some->> symbol source-fn read-string (ann' [] type)))
    (throw (RuntimeException. (str "Unable to resolve symbol: " symbol " in this context")))))

(defmulti special
  (fn [ctx type & exprs]
    (first exprs)))

(defmethod special 'if
  ([ctx type tag]
     (throw (RuntimeException. "Too few arguments to if")))
  ([ctx type tag _]
     (special ctx type tag))
  ([ctx type tag test then]
     (special type tag test then nil))
  ([ctx type tag test then else]
     (all
       (fresh [type] (ann ctx type test))
       (ann' ctx type then)
       (ann' ctx type else)))
  ([ctx type tag _ _ _ & _]
     (throw (RuntimeException. "Too many arguments to if"))))

(defmethod special 'do [ctx type tag & [expr & exprs' :as exprs]]
  (cond (empty? exprs) (== type nil)
        (empty? exprs') (ann ctx type expr)
        :else (all
                (fresh [type] (ann ctx type expr))
                (apply special ctx type tag exprs'))))

(defmethod special 'let* [ctx type tag [var expr & bindings' :as bindings] & exprs]
  (if (empty? bindings)
    (apply special ctx type 'do exprs)
    (fresh [val]
      (ann ctx val expr)
      (apply special (lcons [var val] ctx) type tag bindings' exprs))))

(defna bind [syms params bindings]
  ([[] [] []])
  ([['& sym] [[:seq]] [[sym [:seq]]]])
  ([[sym . syms'] [param . params'] [[sym param] . bindings']]
     (conda [(all
               (is param sym reflect/tag)
               (pred param (complement nil?)))]
            [succeed])
     (bind syms' params' bindings')))

(defn ann-fn [ctx type syms exprs]
  (fresh [params return bindings ctx']
    (== type [:fn params return])
    (bind syms params bindings)
    (appendo (lcons ['recur type] bindings) ctx ctx')
    (apply special ctx' return 'do exprs)))

(defn ann-overloaded [ctx fns [[syms & body] & exprs' :as exprs]]
  (if (empty? exprs)
    (== fns [])
    (fresh [fn fns' ctx']
      (conso fn fns' fns)
      (ann-fn ctx fn syms body)
      (ann-overloaded ctx fns' exprs'))))

(defmethod special 'fn*
  ([ctx type tag] fail)
  ([ctx type tag expr & exprs]
     (cond (seq? expr) (fresh [fns]
                         (conso :overloaded fns type)
                         (ann-overloaded ctx fns (cons expr exprs)))
           (vector? expr) (ann-fn ctx type expr exprs)
           (symbol? expr) (fresh [type']
                            (apply special (lcons [expr type'] ctx) type tag exprs)))))

(defmethod special 'def
  ([ctx type tag name]
     (== type [:var name]))
  ([ctx type tag name expr]
     (fresh [type' self]
       (== type [:var name type'])
       (ann (lcons [name self] ctx) type' expr)
       (<:<' self type'))))

(defmethod special 'quote [ctx type tag & exprs]
  (== type (class (first exprs))))

(defne ->fn [type fn]
  ([[:fn . _] type])
  ([[:var _ type'] _]
     (pred type' (complement lvar?))
     (->fn type' fn))
  ([[:overloaded . fns] _]
     (matche [fns]
       ([[fn . _]])
       ([[_ . fns']]
          (pred fns' (complement lvar?))
          (->fn (lcons :overloaded fns') fn)))))

(defn ann-params [ctx params [arg & args' :as args]]
  (if (empty? args)
    (== params [])
    (fresh [param params']
      (conso param params' params)
      (conde [(pred param #(= % [:seq]))]
             [(ann' ctx param arg)
              (ann-params ctx params' args')]))))

(defn app [ctx type f args]
  (fresh [params]
    (conde [(->fn f [:fn params type])
            (ann-params ctx params args)]
           [(pred f #(isa? % clojure.lang.IFn))])))

(defmethod special 'new [ctx type tag name & args]
  (all
    (== type (resolve name))
    (pred type class?)
    (project [type]
      (app ctx type (cons :overloaded (map #(vector :fn % type) (reflect/constructors type))) args))))

(defn ann-receiver [ctx type expr]
  (conda
   [(all
      (pred expr symbol?)
      (is type expr resolve)
      (pred type class?))]
   [(all
      (ann ctx type expr)
      (pred type class?))]))

(defn ann-field [ctx type expr field]
  (fresh [class]
    (pred field symbol?)
    (ann-receiver ctx class expr)
    (project [field]
      (is type class #(reflect/field % field)))
    (pred type class?)))

(defn ann-method [ctx type expr name & args]
  (fresh [class method]
    (pred name symbol?)
    (ann-receiver ctx class expr)
    (project [class name]
      (app ctx type (cons :overloaded (map #(cons :fn %) (reflect/methods class name))) args))))

(defmethod special '.
  ([ctx type tag obj expr]
     (cond (seq? expr) (apply special ctx type tag obj expr)
           (symbol? expr) (conda [(ann-field ctx type obj expr)]
                                 [(ann-method ctx type obj expr)])))
  ([ctx type tag obj sym & args]
     (apply ann-method ctx type obj sym args)))

(defmethod special 'throw [ctx type tag e]
  (ann' ctx Throwable e))

(defmethod special :default [ctx type f & args]
  (fresh [fn]
    (ann ctx fn f)
    (app ctx type fn args)))

(defmethod special nil [ctx type]
  (== type clojure.lang.PersistentList$EmptyList))

(defn ann [ctx type expr]
  (let [expr (macroexpand expr)]
    (cond (symbol? expr) (conda [(local ctx type expr)]
                                [(global type expr)])
          (seq? expr) (apply special ctx type expr)
          :else (== type (class expr)))))

(defn check [expr]
  (first (run* [type] (condu [(ann [] type expr)]))))
