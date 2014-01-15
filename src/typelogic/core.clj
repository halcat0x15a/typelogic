(ns typelogic.core
  (:refer-clojure :exclude [== isa? resolve])
  (:require [clojure.core :as core]
            [clojure.walk :refer (macroexpand-all)]
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

(def types
  {::fn clojure.lang.AFunction
   ::vec clojure.lang.PersistentVector
   ::seq clojure.lang.ArraySeq
   ::var clojure.lang.Var})

(defn convert [type]
  (if (sequential? type)
    (get types (first type) type)
    type))

(defn isa? [a b]
  (or (and (core/isa? a ::number) (core/isa? b ::number))
      (core/isa? (convert a) (convert b))))

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

(defn ann-do [ctx exprs type]
  (matcha [exprs type]
    ([[] nil])
    ([[expr] _]
       (ann ctx expr type))
    ([[expr . exprs'] _]
       (ann-ctx ctx expr)
       (ann-do ctx exprs' type))))

(defn ann-let [ctx bindings exprs type]
  (matcha [bindings]
    ([[]] (ann-do ctx exprs type))
    ([[var val . bindings']]
       (fresh [ctx' val']
         (ann ctx val val')
         (conso [var val'] ctx ctx')
         (ann-let ctx' bindings' exprs type)))))

(defn tag [symbol type]
  (fresh [tag]
    (is tag symbol (comp :tag meta))
    (pred tag (complement nil?))
    (is type tag reflect/tag->class)))

(defna ann-params [params types bindings]
  ([[] [] []])
  ([['& param] [::seq] [[param ::seq]]])
  ([[param . params'] [type . types'] [[param type] . bindings']]
     (conda [(tag param type)]
            [succeed])
     (ann-params params' types' bindings')))

(defn ann-fn [ctx params exprs type]
  (matcha [type]
    ([[::fn return . types]]
       (fresh [bindings ctx']
         (ann-params params types bindings)
         (appendo bindings ctx ctx')
         (ann-do ctx' exprs return)))))

(defn ann-fns [ctx exprs type]
  (matcha [exprs]
    ([[[params . body] . exprs']]
       (conde [(ann-fn ctx params body type)]
              [(ann-fns ctx exprs' type)]))))

(defn ann-fn' [ctx exprs type]
  (matcha [exprs]
    ([[params . exprs']]
       (pred params vector?)
       (ann-fn ctx params exprs' type))
    ([_] (ann-fns ctx exprs type))))

(defn resolve [symbol type]
  (all
    (pred symbol symbol?)
    (is type symbol core/resolve)))

(defn resolve-fn [symbol type]
  (fresh [expr type']
    (is expr symbol #(some-> % source-fn read-string macroexpand-all))
    (pred expr (complement nil?))
    (ann [] expr type')
    (matcha [type'] ([[::var _ type]]))))

(defn ann-var [ctx expr type]
  (all
   (pred expr symbol?)
   (project [expr ctx]
     (util/every type (->> ctx (filter #(= (first %) expr)) (map second))))))

(defn ann-val [expr type]
  (fresh [expr' type']
    (conda [(resolve expr expr')
            (conda [(pred expr' class?)
                    (== type expr')]
                   [(pred expr' var?)
                    (project [expr'] (resolve-fn (-> expr' meta :name) type))])]
           [(is type expr class)])))

(defna app [ctx exprs types]
  ([_ [] []])
  ([_ [expr . exprs'] [type . types']]
     (fresh [type']
       (ann ctx expr type')
       (conda [(== type type')]
              [(project [type type'] (== true (isa? type' type)))])
       (app ctx exprs' types')))
  ([_ _ [type]]
     (pred type (partial = ::seq))))

(defn app' [ctx operator operands type]
  (matcha [operator]
    ([[::fn type . types]]
       (app ctx operands types))))

(defn call [ctx obj msg args type]
  (fresh [obj' msg']
    (pred msg symbol?)
    (conda [(resolve obj obj')]
           [(tag obj obj')]
           [(ann ctx obj obj')])
    (pred obj' class?)
    (project [obj' msg]
      (conda [(util/every type (reflect/fields obj' msg))]
             [(util/every msg' (reflect/methods obj' msg))
              (app' ctx msg' args type)]))))

(defn construct [ctx class args type]
  (fresh [constructor]
    (resolve class type)
    (pred type class?)
    (project [type] (util/every constructor (reflect/constructors type)))
    (app' ctx constructor args type)))

(defn ann [ctx expr type]
  (matcha [expr type]
    ([['def name] [::var name type']])
    ([['def name expr'] [::var name type']]
       (fresh [ctx']
         (conso [name type'] ctx ctx')
         (ann ctx' expr' type')))
    ([['if test then] _]
       (ann-if ctx test then nil type))
    ([['if test then else] _]
       (ann-if ctx test then else type))
    ([['do . exprs] _]
       (ann-do ctx exprs type))
    ([['let* bindings . exprs] _]
       (ann-let ctx bindings exprs type))
    ([['quote expr'] _]
       (is type expr' class))
    ([['fn* name . exprs] _]
       (fresh [ctx']
         (pred name symbol?)
         (conso [name type] ctx ctx')
         (ann-fn' ctx' exprs type)))
    ([['fn* . exprs] _]
       (ann-fn' ctx exprs type))
    ([['loop* bindings . exprs] _]
       (ann-let ctx bindings exprs type))
    ([['recur . exprs] _]
       (everyg (partial ann-ctx ctx) exprs))
    ([['throw expr'] _] (ann-ctx ctx expr'))
    ([[dot obj [method . args]] _]
       (== dot '.)
       (call ctx obj method args type))
    ([[dot obj method . args] _]
       (== dot '.)
       (call ctx obj method args type))
    ([['new class . args] _]
       (construct ctx class args type))
    ([[operator . operands] _]
       (pred expr seq?)
       (fresh [operator']
         (ann ctx operator operator')
         (app' ctx operator' operands type)))
    ([_ [::vec . types]]
       (pred expr vector?)
       (app ctx expr types))
    ([_ _]
       (pred expr (complement seq?))
       (conda [(ann-var ctx expr type)]
              [(ann-val expr type)]))))

(defn check
  ([expr]
     (check [] expr))
  ([ctx expr]
     (run *n* [type] (ann ctx (macroexpand-all expr) type))))
