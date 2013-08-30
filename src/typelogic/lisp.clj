(ns typelogic.lisp
  (:refer-clojure :exclude [==])
  (:require [clojure.walk :refer (macroexpand-all)]
            [clojure.reflect :refer (reflect)]
            [clojure.repl :refer (source-fn)]
            [clojure.core.logic :refer :all]))

(def ^:dynamic *depth* 10)

(declare ann)

(defna tag [tag type]
  (['long _] (== type Long/TYPE))
  (['double _] (== type Double/TYPE))
  ([_ _]
     (pred tag symbol?)
     (is type tag resolve)))

(defna bind [ctx ctx' names types]
  ([_ ctx [] []])
  ([_ [[name type] . ctx''] ['& _] [type]] (== type clojure.lang.ArraySeq))
  ([_ [[name type] . ctx''] [name . names'] [type . types']]
     (bind ctx ctx'' names' types')
     (conda [(pred name #(contains? (meta %) :tag))
             (project [name] (tag (-> name meta :tag) type))]
            [s#])))

(defn ann-if [ctx predicate consequence alternative type]
  (all (fresh [type'] (ann ctx predicate type'))
       (conde [(ann ctx consequence type)]
              [(ann ctx alternative type)])))

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

(defna subtyping [subs supers]
  ([[] []])
  ([[type . subs'] [type . supers']] (subtyping subs' supers'))
  ([_ [type]] (pred type (partial = clojure.lang.ArraySeq)))
  ([[sub . subs'] [super . supers']]
     (project [sub super] (== true (isa? sub super)))
     (subtyping subs' supers')))

(defna app [operator operands type]
  ([[::-> supertypes type] _ _] (subtyping operands supertypes)))

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

(defn source [sym]
  (some-> sym source-fn read-string macroexpand-all))

(defn immediate [expr type]
  (conda [(pred expr integer?) (== type Long/TYPE)]
         [(pred expr float?) (== type Double/TYPE)]
         [(pred expr symbol?)
          (fresh [expr']
            (is expr' expr source)
            (pred expr' (complement nil?))
            (ann [] expr' type))]
         [(is type expr class)]))

(defn call [ctx dot instance method arguments type]
  (all (pred dot (partial = '.))
       (pred method symbol?)
       (fresh [class arguments']
         (conda [(pred instance symbol?)
                 (is class instance resolve)
                 (pred class class?)]
                [(ann ctx instance class)])
         (form ctx arguments arguments')
         (project [class method]
           (attempt (reflection class method) arguments' type)))))

(defna ann [ctx expr type]
  ([_ ['def _] _] u#)
  ([_ ['def name expr'] _]
     (fresh [ctx']
       (conso [name type] ctx ctx')
       (ann ctx' expr' type)))
  ([_ ['fn* name . functions] _]
     (pred name symbol?)
     (fresh [ctx']
       (conso [name type] ctx ctx')
       (ann-fn ctx functions type)))
  ([_ ['fn* . functions] _] (ann-fn ctx functions type))
  ([_ ['if predicate consequence] _]
     (ann-if ctx predicate consequence nil type))
  ([_ ['if predicate consequence alternative] _]
     (ann-if ctx predicate consequence alternative type))
  ([_ ['let* bindings body] _] (ann-let ctx bindings body type))
  ([_ ['do . exprs] _] (ann-do ctx exprs type))
  ([_ ['quote expr'] _] (immediate expr' type))
  ([_ ['new class . _] _] (is type class resolve))
  ([_ ['recur . _] _] u#)
  ([_ ['throw . _] _] u#)
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
