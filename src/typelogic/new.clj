(ns typelogic.new
  (:refer-clojure :exclude [== record?])
  (:require [clojure.walk :refer [macroexpand-all]]
            [clojure.repl :refer [source-fn]]
            [clojure.core.match :refer [match]]
            [clojure.core.logic :refer :all]
            [clojure.core.logic.pldb :as pldb]
            [typelogic.reflect :as reflect]))

(declare ann)

(def ^:dynamic *db* pldb/empty-db)

(pldb/db-rel local type name)

(defmulti convert
  (fn [type]
    (cond (sequential? type) (first type)
          (class? type) type)))

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
(defmethod convert nil [_] Object)
(defmethod convert :default [type] type)

(defn <:< [a b]
  (or (and (nil? a) (isa? b Object))
      (and (isa? a Number) (isa? b Number))
      (isa? a b)))

(defn any [f xs]
  (matche [xs]
    ([[x . _]] (f x))
    ([[_ . xs']]
       (any f xs'))))

(defn ann' [ctx type expr]
  (fresh [sub]
    (ann ctx sub expr)
    (conde [(== type sub)]
           [(project [sub] (predc type #(<:< (convert sub) (convert %)) (fn [_ _ r s] (list sub '<:< (-reify s type r)))))])))

(defn local [ctx type sym]
  (matcha [ctx]
    ([[[sym type] . _]])
    ([[_ . ctx']]
       (local ctx' type sym))))

(defn global [type symbol]
  (if-let [var (resolve symbol)]
    (if (class? var)
      (== type Class)
      (some->> symbol source-fn read-string (ann [] type)))
    (throw (RuntimeException. (str "Unable to resolve symbol: " symbol " in this context")))))

(defmulti special
  (fn [ctx type & exprs]
    (first exprs)))

(defmethod special 'if
  ([ctx type tag test then]
     (special type tag test then nil))
  ([ctx type tag test then else]
     (condu [(all
              (fresh [type] (ann ctx type test))
              (ann' ctx type then)
              (ann' ctx type else))])))

(defmethod special 'do [ctx type tag & exprs]
  (match [exprs]
    [([] :seq)] (== type nil)
    [([expr] :seq)] (ann ctx type expr)
    [([expr & exprs'] :seq)]
      (all
       (fresh [type] (ann ctx type expr))
       (apply special ctx type tag exprs'))))

(defmethod special 'let* [ctx type tag bindings & exprs]
  (match [bindings]
    [([] :seq)] (apply special ctx type 'do exprs)
    [([var val & bindings'] :seq)]
      (fresh [val']
        (ann ctx val' val)
        (apply special (lcons [var val'] ctx) type tag bindings' exprs))))

(defna bind [syms params bindings]
  ([[] [] []])
  ([['& sym] [[:seq]] [[sym [:seq]]]])
  ([[sym . syms'] [param . params'] [[sym param] . bindings']]
     (conda [(all
               (is param sym reflect/tag)
               (pred param (complement nil?)))]
            [succeed])
     (bind syms' params' bindings')))

(defn ann-fn [ctx type syms & exprs]
  (fresh [params return bindings ctx']
    (== type [:fn params return])
    (bind syms params bindings)
    (appendo (lcons ['recur type] bindings) ctx ctx')
    (apply special ctx' return 'do exprs)))

(defmethod special 'fn*
  ([ctx type tag] fail)
  ([ctx type tag expr & exprs]
     (cond (seq? expr)
             (conde [(condu [(apply ann-fn ctx type expr)])]
                    [(pred exprs (complement empty?))
                     (apply special ctx type tag exprs)])
           (vector? expr) (apply ann-fn ctx type expr exprs)
           (symbol? expr)
             (fresh [type']
               (apply special (lcons [expr type'] ctx) type tag exprs)
               (condu
                [(== type type')]
                [(fresh [type]
                   (apply special (lcons [expr type] ctx) type' tag exprs))])))))

(defmethod special 'def
  ([ctx type tag name]
     (== type [:var name]))
  ([ctx type tag name expr]
     (fresh [type']
       (== type [:var name type'])
       (ann (lcons [name type] ctx) type' expr))))

(defmethod special 'quote [ctx type tag & exprs]
  (== type (class (first exprs))))

(defn app [ctx params args]
  (match [args]
    [([] :seq)] (== params [])
    [([arg & args'] :seq)]
      (fresh [param params']
        (conso param params' params)
        (ann' ctx param arg)
        (app ctx params' args'))))

(defmethod special 'new [ctx type tag name & args]
  (all
   (== type (resolve name))
   (pred type class?)
   (project [type]
     (any #(app ctx % args) (reflect/constructors type)))))

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
      (any #(== method %) (reflect/methods class name)))
    (matcha [method] ([[type . params]] (app ctx params args)))))

(defmethod special '.
  ([ctx type tag obj expr]
     (cond (seq? expr) (apply special ctx type tag obj expr)
           (symbol? expr) (conda [(ann-field ctx type obj expr)]
                                 [(ann-method ctx type obj expr)])))
  ([ctx type tag obj sym & args]
     (apply ann-method ctx type obj sym args)))

(defna ->fn [type fn]
  ([[:fn . _] type])
  ([[:var _ fn] _]))

(defmethod special :default [ctx type f & args]
  (fresh [ifn params]
    (ann ctx ifn f)
    (->fn ifn [:fn params type])
    (app ctx params args)))

(defn ann [ctx type expr]
  (let [expr (macroexpand expr)]
    (cond (symbol? expr) (conda [(local ctx type expr)]
                                [(global type expr)])
          (seq? expr) (apply special ctx type expr)
          :else (== type (class expr)))))

(defn check [expr]
  (doall (run* [type] (ann [] type expr))))
;7.3.4
:seq
#_(binding [*ns* (the-ns 'clojure.core)]
  (check '(fn concat [x y]
    (lazy-seq
      (let [s (seq x)]
        (if s
          (if (chunked-seq? s)
            (chunk-cons (chunk-first s) (concat (chunk-rest s) y))
            (cons (first s) (concat (rest s) y)))
          y))))))
(check '(fn [chunk rest]
          (clojure.lang.RT/count chunk)
          (clojure.lang.ChunkedCons. chunk rest)))

#_(run* [q] (fresh [a b]
            (== q [a b])
            (condu [(conde [(== a 1)] [(== b 0)])
                    (conde [(== a 1)] [(== b 1)])])))
