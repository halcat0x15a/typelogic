(ns typelogic.core
  (:refer-clojure :exclude [==])
  (:require [clojure.walk :refer (walk macroexpand-all)]
            [clojure.repl :refer (source-fn)]
            [clojure.core.logic :refer :all]
            [typelogic.reflect :as reflect]
            [typelogic.util :as util]))

(def ^:dynamic *n* 15)

(declare ann)

(defn ann-ctx [ctx expr]
  (fresh [type]
    (ann ctx expr type)))

(defn ann-if [ctx test then else type]
  (all (ann-ctx ctx test)
       (conde [(all (ann ctx then type)
                    (ann-ctx ctx else))]
              [(all (ann-ctx ctx then)
                    (ann ctx else type))])))

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
  (all (pred symbol (comp boolean :tag meta))
       (is type symbol (comp reflect/tag->class :tag meta))))

(defna ann-params [params types bindings]
  ([[] [] []])
  ([['& param] [::seq] [[param ::seq]]])
  ([[param . params'] [type . types'] [[param type] . bindings']]
     (conda [(tag param type)]
            [succeed])
     (ann-params params' types' bindings')))

(defne ann-fn [ctx fns type]
  ([_ [params . exprs] [::fn return . types]]
     (pred params vector?)
     (fresh [bindings ctx']
       (ann-params params types bindings)
       (appendo bindings ctx ctx')
       (ann-do ctx' exprs return)))
  ([_ [expr . _] _]
     (ann-fn ctx expr type))
  ([_ [_ . fns'] type]
     (ann-fn ctx fns' type)))

(defn ann-val [expr type]
  (is type expr reflect/infer))

(defna ann-var [ctx expr type]
  ([[[expr type] . _] _ _])
  ([[_ . ctx'] _ _]
     (ann-var ctx' expr type)))

(defna ann-list [ctx exprs types]
  ([_ [] []])
  ([_ [expr . exprs'] [type . types']]
     (fresh [type']
       (ann ctx expr type')
       (conda [(project [type type'] (== true (reflect/isa? type' type)))]
              [(== type type')])
       (ann-list ctx exprs' types')))
  ([_ _ [type]]
     (pred type (partial = ::seq))))

(defna app [ctx operator operands type]
  ([_ [::fn type . types] _ _]
     (ann-list ctx operands types)))

(defn resolve-class [symbol type]
  (all (pred symbol symbol?)
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
              (app ctx msg' args type)]))))

(defn construct [ctx class args type]
  (fresh [constructor]
    (resolve-class class type)
    (project [type] (util/every constructor (reflect/constructors type)))
    (app ctx constructor args type)))

(defna ann [ctx expr type]
  ([_ ['def name] [::var name]])
  ([_ ['def name expr'] [::var name type'']]
     (ann ctx expr' type''))
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
  ([_ ['recur . _] _] fail)
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
     (fresh [operator']
       (ann ctx operator operator')
       (app ctx operator' operands type)))
  ([_ _ _]
     (pred expr (complement seq?))
     (conda [(ann-var ctx expr type)]
            [(ann-val expr type)])))

(defn check
  ([expr]
     (check [] expr))
  ([ctx expr]
     (run *n* [type] (ann ctx (macroexpand-all expr) type))))
