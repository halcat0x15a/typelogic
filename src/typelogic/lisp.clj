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
     (bind ctx ctx'' names' types')))

(defna form [ctx exprs types]
  ([_ [] []])
  ([_ [expr . exprs'] [type . types']]
     (ann ctx expr type)
     (form ctx exprs' types')))

(defna ann [ctx expr type]
  ([_ ['fn parameters body] [::-> types return]]
    (fresh [ctx']
      (bind ctx ctx' parameters types)
      (ann ctx' body return)))
  ([_ ['if _ consequence] _] (-if ctx consequence nil type))
  ([_ ['if _ consequence alternative] _] (-if ctx consequence alternative type))
  ([_ ['let bindings body] _] (-let ctx bindings body type))
  ([_ ['do . exprs] _] (-do ctx exprs type))
  ([_ [[::-> parameters type] . parameters] _])
  ([_ [operator . operands] _]
     (fresh [type' types' expr']
       (ann ctx operator type')
       (form ctx operands types')
       (conso type' types' expr')
       (ann ctx expr' type)))
  ([[[name type] . _] name _])
  ([[_ . ctx'] _ _] (ann ctx' expr type))
  ([_ _ _] (project [expr] (== type (class expr)))))

(defn check [expr] (first (run* [type] (ann [] expr type))))
