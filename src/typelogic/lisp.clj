(ns typelogic.lisp
  (:refer-clojure :exclude [==])
  (:require [clojure.walk :refer (macroexpand-all)]
            [clojure.reflect :refer (reflect)]
            [clojure.repl :refer (source-fn)]
            [clojure.core.logic :refer :all]
            [clojure.core.logic.dcg :refer :all]))

(def ^:dynamic *depth* 5)

(declare ann)

(defn -if [ctx consequence alternative type]
  (conde [(conda [(ann ctx consequence type)
                  (ann ctx alternative type)])]
         [(conde [(ann ctx consequence type)]
                 [(ann ctx alternative type)])]))

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

(defna form [ctx exprs types]
  ([_ [] []])
  ([_ [expr . exprs'] [type . types']]
     (ann ctx expr type)
     (form ctx exprs' types')))

(defna subtyping [subtypes supertypes]
  ([[] []])
  ([[subtype . subtypes'] [supertype . supertypes']]
     (project [subtype supertype] (== true (isa? subtype supertype)))
     (subtyping subtypes' supertypes')))

(defna app [operator operands type]
  ([[::-> operands type] operands _])
  ([[::-> supertypes type] _ _]
     (subtyping operands supertypes)))

(defne attempt [operators operands type]
  ([[operator . _] _ _] (app operator operands type))
  ([[_ . operators'] _ _] (attempt operators' operands type)))

(defn tag [name type]
  (conda [(project [name] (== type (some-> name meta :tag resolve)))
          (pred type class?)]))

(defna bind [ctx ctx' names types]
  ([_ ctx [] []])
  ([_ [[name type] . ctx''] [name . names'] [type . types']]
     (conda [(tag name type)
             (bind ctx ctx'' names' types')]
            [(bind ctx ctx'' names' types')])))

(defne abs [ctx functions type]
  ([_ [[parameters body] . _] [::-> types return]]
     (fresh [ctx']
       (bind ctx ctx' parameters types)
       (ann ctx' body return)))
  ([_ [_ . functions'] _] (abs ctx functions' type)))

(defna variable [ctx expr type]
  ([[[expr type] . _] expr _])
  ([[_ . ctx'] _ _] (ann ctx' expr type)))

(defn reflection [instance method]
  (some->>
   instance
   resolve
   reflect
   :members
   (filter #(= (:name %) method))
   (map #(list ::-> (map resolve (:parameter-types %)) (resolve (:return-type %))))))

(defne ann [ctx expr type]
  ([_ ['def name expr'] [::def name type']] (ann ctx expr' type'))
  ([_ ['fn* . functions] _] (abs ctx functions type))
  ([_ ['if _ consequence] _] (-if ctx consequence nil type))
  ([_ ['if _ consequence alternative] _] (-if ctx consequence alternative type))
  ([_ ['let* bindings body] _] (-let ctx bindings body type))
  ([_ ['do . exprs] _] (-do ctx exprs type))
  ([_ ['quote] nil])
  ([_ ['quote expr' . _] _] (project [expr'] (== type (class expr'))))
  ([_ [dot instance [method . arguments]] _]
     (fresh [arguments']
       (== '. dot)
       (form ctx arguments arguments')
       (project [instance method]
         (attempt (reflection instance method) arguments' type))))
  ([_ ['new type' . _] _] (project [type'] (== type (resolve type'))))
  ([_ [operator . operands] _]
     (fresh [operator' operands']
       (ann ctx operator operator')
       (form ctx operands operands')
       (app operator' operands' type)))
  ([_ _ _] (variable ctx expr type))
  ([_ _ _]
     (project [expr]
       (== false (symbol? expr))
       (== false (seq? expr))
       (== type (class expr)))))

(defn check [expr]
  (set (run *depth* [type] (ann [] (macroexpand-all expr) type))))

(defn check-fn [sym]
  (-> sym source-fn read-string check))
