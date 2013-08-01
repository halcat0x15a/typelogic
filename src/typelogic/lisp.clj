(ns typelogic.lisp
  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic :refer :all]
            [clojure.core.logic.dcg :refer :all]))

(declare ann)

(defne -if [ctx consequence alternative type]
  ([_ _ _ _]
     (ann ctx consequence type)
     (ann ctx alternative type))
  ([_ _ _ [::+ left right]]
     (ann ctx consequence right)
     (ann ctx alternative left)))

(defna -let [ctx bindings body type]
  ([_ [] _ _] (ann ctx body type))
  ([_ [var val . bindings'] _ _]
     (fresh [ctx' type']
       (ann ctx val type')
       (conso [var type'] ctx ctx')
       (-let ctx' bindings' body type))))

(defna -do [ctx exprs type]
  ([_ [] nil])
  ([_ [expr] _] (ann ctx expr type))
  ([_ [_ . exprs'] _] (-do ctx exprs' type)))

(defna bind [ctx ctx' names types]
  ([_ ctx [] []])
  ([_ [[name type] . ctx''] [name . names'] [type . types']]
     (fresh [tag]
       (project [name] (== tag (some-> name meta :tag resolve)))
       (conda [(pred tag class?)
               (== type tag)
               (bind ctx ctx'' names' types')]
              [(bind ctx ctx'' names' types')]))))

(defna form [ctx exprs types]
  ([_ [] []])
  ([_ [expr . exprs'] [type . types']]
     (ann ctx expr type)
     (form ctx exprs' types')))

(defna app [operator operands type] ([[::-> parameters type] parameters _]))

(defna ann [ctx expr type]
  ([[[name type]] ['def name expr'] _] (ann ctx expr' type))
  ([[] ['fn parameters body] [::-> types return]]
     (fresh [ctx']
       (bind ctx ctx' parameters types)
       (ann ctx' body return)))
  ([[] ['if _ consequence] _] (-if ctx consequence nil type))
  ([[] ['if _ consequence alternative] _] (-if ctx consequence alternative type))
  ([[] ['let bindings body] _] (-let ctx bindings body type))
  ([[] ['do . exprs] _] (-do ctx exprs type))
  ([[] [operator . operands] _]
     (fresh [type' types']
       (ann ctx operator type')
       (form ctx operands types')
       (app type' types' type)))
  ([[[name type] . _] name _])
  ([[_ . ctx'] _ _] (ann ctx' expr type))
  ([[] _ _]
     (project [expr]
       (== false (class? expr))
       (== type (class expr)))))

(defn check [expr]
  (first (run 1 [q] (fresh [env type] (ann env expr type) (== q [env type])))))
