(ns typelogic.core
  (:refer-clojure :exclude [== isa?])
  (:require [clojure.core :as core]
            [clojure.walk :refer (walk macroexpand-all)]
            [clojure.repl :refer (source-fn)]
            [clojure.core.logic :refer :all]
            [typelogic.reflect :as reflect]
            [typelogic.util :as util]))

(def ^:dynamic *n* 15)

(declare ann)

(derive Long ::number)
(derive Integer ::number)
(derive Double ::number)
(derive Float ::number)
(derive Long/TYPE ::number)
(derive Integer/TYPE ::number)
(derive Double/TYPE ::number)
(derive Float/TYPE ::number)

(defn convert [type]
  (if (coll? type)
    (case (first type)
      ::fn clojure.lang.Fn
      ::vec clojure.lang.PersistentVector
      ::seq clojure.lang.ArraySeq
      type)
    type))

(defmulti isa? (fn [a b] [a b]))
(defmethod isa? [::number ::number] [_ _] true)
(defmethod isa? :default [a b] (core/isa? (convert a) (convert b)))

(defn ann-ctx [ctx expr]
  (fresh [type]
    (ann ctx expr type)))

(defn ann-if [ctx test then else type]
  (all
    (ann-ctx ctx test)
    (conda [(ann ctx then type)
            (ann ctx else type)]
           [(conde [(ann ctx then type)
                    (ann-ctx ctx else)]
                   [(ann-ctx ctx then)
                    (ann ctx else type)])])))

(defna ann-do [ctx exprs type]
  ([_ [] nil])
  ([_ [expr] _]
     (ann ctx expr type))
  ([_ [expr . exprs'] _]
     (ann-ctx ctx expr)
     (ann-do ctx exprs' type)))

(defna ann-let [ctx bindings exprs type]
  ([_ [] _ _]
     (ann-do ctx exprs type))
  ([_ [var val . bindings'] _ _]
     (fresh [ctx' val']
       (ann ctx val val')
       (conso [var val'] ctx ctx')
       (ann-let ctx' bindings' exprs type))))

(defn tag [symbol type]
  (all
    (pred symbol (comp boolean :tag meta))
    (is type symbol (comp reflect/tag->class :tag meta))))

(defna ann-params [params types bindings]
  ([[] [] []])
  ([['& param] [::seq] [[param ::seq]]])
  ([[param . params'] [type . types'] [[param type] . bindings']]
     (conda [(tag param type)]
            [succeed])
     (ann-params params' types' bindings')))

(defna ann-fn [ctx exprs type]
  ([_ [params . exprs'] [::fn return . types]]
     (pred params vector?)
     (fresh [bindings ctx']
       (ann-params params types bindings)
       (appendo bindings ctx ctx')
       (ann-do ctx' exprs' return)))
  ([_ [expr . exprs'] _]
     (pred exprs seq?)
     (conde [(ann-fn ctx expr type)]
            [(ann-fn ctx exprs' type)])))

(defna ann-var [ctx expr type]
  ([[[expr type] . _] _ _])
  ([[_ . ctx'] _ _]
     (ann-var ctx' expr type)))

(defn ann-val [expr type]
  (is type expr reflect/infer))

(defna app [ctx exprs types]
  ([_ [] []])
  ([_ [expr . exprs'] [type . types']]
     (fresh [type']
       (ann ctx expr type')
       (conda [(project [type type'] (== true (isa? type' type)))]
              [(== type type')])
       (app ctx exprs' types')))
  ([_ _ [type]]
     (pred type (partial = ::seq))))

(defn resolve-class [symbol type]
  (all
    (pred symbol symbol?)
    (is type symbol reflect/symbol->class)
    (pred type (complement nil?))))

(defn call [ctx obj msg args type]
  (fresh [obj' msg']
    (pred msg symbol?)
    (conda [(resolve-class obj obj')]
           [(tag obj obj')]
           [(ann ctx obj obj')])
    (pred obj' class?)
    (project [obj' msg]
      (conda [(util/every type (reflect/fields obj' msg))]
             [(util/every msg' (reflect/methods obj' msg))
              (matcha [msg'] ([[type . types]] (app ctx args types)))]))))

(defn construct [ctx class args type]
  (fresh [constructor]
    (resolve-class class type)
    (project [type] (util/every constructor (reflect/constructors type)))
    (matcha [constructor] ([[type . types]] (app ctx args types)))))

(defna ann [ctx expr type]
  ([_ ['def name] [::var name]])
  ([_ ['def name expr'] [::var name type']]
     (fresh [ctx']
       (conso [name type'] ctx ctx')
       (ann ctx' expr' type')))
  ([_ ['if test then] _]
     (ann-if ctx test then nil type))
  ([_ ['if test then else] _]
     (ann-if ctx test then else type))
  ([_ ['do . exprs] _]
     (ann-do ctx exprs type))
  ([_ ['let* bindings . exprs] _]
     (ann-let ctx bindings exprs type))
  ([_ ['quote _] _]
     (ann-val expr type))
  ([_ ['fn* name . exprs] _]
     (fresh [ctx']
       (pred name symbol?)
       (conso [name type] ctx ctx')
       (ann-fn ctx' exprs type)))
  ([_ ['fn* . exprs] _]
     (ann-fn ctx exprs type))
  ([_ ['loop* bindings . exprs] _]
     (ann-let ctx bindings exprs type))
  ([_ ['recur . exprs] _]
     (everyg (partial ann-ctx ctx) exprs))
  ([_ ['throw _] _] fail)
  ([_ [dot obj [method . args]] _]
     (== dot '.)
     (call ctx obj method args type))
  ([_ [dot obj method . args] _]
     (== dot '.)
     (call ctx obj method args type))
  ([_ ['new class . args] _]
     (construct ctx class args type))
  ([_ [operator . operands] _]
     (pred expr seq?)
     (fresh [operator']
       (ann ctx operator operator')
       (matcha [operator'] ([[::fn type . types]] (app ctx operands types)))))
  ([_ _ [::vec . types]]
     (pred expr vector?)
     (app ctx expr types))
  ([_ _ _]
     (pred expr (complement seq?))
     (conda [(ann-var ctx expr type)]
            [(ann-val expr type)])))

(defn check
  ([expr]
     (check [] expr))
  ([ctx expr]
     (run *n* [type] (ann ctx (macroexpand-all expr) type))))
