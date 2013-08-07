(ns typelogic.lisp
  (:refer-clojure :exclude [==])
  (:require [clojure.walk :refer (macroexpand-all)]
            [clojure.reflect :refer (reflect)]
            [clojure.repl :refer (source-fn)]
            [clojure.core.logic :refer :all]
            [clojure.core.logic.dcg :refer :all]))

(def ^:dynamic *depth* 10)

(defmacro error [s]
  `(fn [a#] (prn ~s) nil))

(declare ann)

(defna bind [ctx ctx' names types]
  ([_ ctx [] []])
  ([_ [[name type] . ctx''] ['& . _] [type]] (== type clojure.lang.ArraySeq))
  ([_ [[name type] . ctx''] [name . names'] [type . types']]
     (conda [(conda [(is type name #(some-> % meta :tag resolve))
                     (pred type class?)])
             (bind ctx ctx'' names' types')]
            [(bind ctx ctx'' names' types')])))

(defn ann-if [ctx consequence alternative type]
  (conde [(conda [(ann ctx consequence type)
                  (ann ctx alternative type)])]
         [(conde [(ann ctx consequence type)]
                 [(ann ctx alternative type)])]))

(defna ann-let [ctx bindings body type]
  ([_ [] _ _] (ann ctx body type))
  ([_ [var val . bindings'] _ _]
     (fresh [ctx' type']
       (ann ctx val type')
       (bind ctx ctx' [var] [type'])
       (ann-let ctx' bindings' body type))))

(defna ann-do [ctx exprs type]
  ([_ [] nil])
  ([_ [expr] _] (ann ctx expr type))
  ([_ [_ . exprs'] _] (ann-do ctx exprs' type)))

(defne ann-fn [ctx functions type]
  ([_ [[parameters body] . _] [::-> types return]]
     (fresh [ctx']
       (bind ctx ctx' parameters types)
       (ann ctx' body return)))
  ([_ [_ . functions'] _] (ann-fn ctx functions' type)))

(defna form [ctx exprs types]
  ([_ [] []])
  ([_ [expr . exprs'] [type . types']]
     (ann ctx expr type)
     (form ctx exprs' types')))

(defna subtyping [subtypes supertypes]
  ([[] []])
  ([[type . subtypes'] [type . supertypes']] (subtyping subtypes' supertypes'))
  ([_ [type]] (== type clojure.lang.ArraySeq))
  ([[subtype . subtypes'] [supertype . supertypes']]
     (project [subtype supertype] (== true (isa? subtype supertype)))
     (subtyping subtypes' supertypes')))

(defna app [operator operands type]
  ([[::-> supertypes type] _ _]
     (subtyping operands supertypes)))

(defne attempt [operators operands type]
  ([[operator . _] _ _] (app operator operands type))
  ([[_ . operators'] _ _] (attempt operators' operands type)))

(defn reflection [class method]
  (->> class
       .getMethods
       (filter #(= (.getName %) (name method)))
       (map #(list ::-> (vec (.getParameterTypes %)) (.getReturnType %)))))

(defna variable [ctx expr type]
  ([[[expr type] . _] expr _])
  ([[_ . ctx'] _ _] (variable ctx' expr type)))

(defn immediate [expr type]
    (conda [(pred expr symbol?)
            (fresh [expr']
              (is expr' expr #(some-> % source-fn read-string macroexpand-all))
              (conda [(pred expr' (complement nil?))
                      (ann [] expr' type)]
                     [(fresh [var]
                        (is var expr resolve)
                        (pred var var?)
                        (is type var (comp class var-get)))]
                     [(project [expr]
                        (error (str "Unable to resolve symbol: " expr)))]))]
           [(conde [(pred expr integer?) (== type 'long)]
                   [(pred expr float?) (== type 'double)]
                   [(is type expr class)])]))

(defn call [ctx dot instance method arguments type]
  (conda [(== '. dot)
          (pred method symbol?)
          (fresh [class arguments']
            (form ctx arguments arguments')
            (conde [(pred instance symbol?)
                    (is class instance resolve)]
                   [(ann ctx instance class)])
            (conda [(pred class class?)
                    (project [class method]
                      (attempt (reflection class method) arguments' type))]
                   [(project [instance]
                      (error (str "Unable to typed symbol: " instance)))]))]))

(defna ann [ctx expr type]
  ([_ ['def name expr'] _]
     (fresh [ctx']
       (conso [name type] ctx ctx')
       (ann ctx' expr' type)))
  ([_ ['fn* name . functions] _]
     (pred name symbol?)
     (ann-fn ctx functions type))
  ([_ ['fn* . functions] _] (ann-fn ctx functions type))
  ([_ ['if _ consequence] _]
     (ann-if ctx consequence nil type))
  ([_ ['if _ consequence alternative] _]
     (ann-if ctx consequence alternative type))
  ([_ ['let* bindings body] _] (ann-let ctx bindings body type))
  ([_ ['do . exprs] _] (ann-do ctx exprs type))
  ([_ ['quote] nil])
  ([_ ['quote expr' . _] _] (immediate expr' type))
  ([_ ['new class . _] _] (is type class resolve))
  ([_ ['recur . _] _] u#)
  ([_ [dot instance [method . arguments]] _]
     (call ctx dot instance method arguments type))
  ([_ [dot instance method . arguments] _]
     (call ctx dot instance method arguments type))
  ([_ [operator . operands] _]
     (fresh [operator' operands']
       (ann ctx operator operator')
       (form ctx operands operands')
       (app operator' operands' type)))
  ([_ _ _] (variable ctx expr type))
  ([_ _ _] (immediate expr type)))

(defn check [expr]
  (set (run *depth* [type] (ann [] (macroexpand-all expr) type))))
