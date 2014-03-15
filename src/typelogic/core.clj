(ns typelogic.core
  (:refer-clojure :exclude [isa? == methods])
  (:require [clojure.core :as core]
            [clojure.walk :refer [macroexpand-all]]
            [clojure.repl :refer [source-fn]]
            [clojure.core.logic :refer :all]
            [clojure.core.logic.protocols :refer [lfirst]]
            [typelogic.reflect :as reflect]
            [typelogic.util :refer :all])
  (:import [java.lang.reflect Modifier Method Field Constructor]))

(def ^:dynamic *n* 15)
(def ^:dynamic *env* [])

(declare ann)
(declare check)

(def primitives
  {Boolean/TYPE Boolean
   Character/TYPE Character
   Byte/TYPE Byte
   Short/TYPE Short
   Integer/TYPE Integer
   Long/TYPE Long
   Float/TYPE Float
   Double/TYPE Double})

(def literals
  {::fn clojure.lang.AFunction
   ::vec clojure.lang.PersistentVector
   ::seq clojure.lang.ArraySeq
   ::var clojure.lang.Var})

(defn convert [type]
  (cond (class? type) (get primitives type type)
        (keyword? type) (get literals type)
        (sequential? type) (get literals (first type))
        (lcons? type) (get literals (lfirst type))
        (lvar? type) Object))

(defn isa? [a b]
  (let [a (convert a)
        b (convert b)]
    (or (and (core/isa? b Object) (nil? a))
        (and (core/isa? b Number) (core/isa? a Number))
        (core/isa? a b))))

(defn final? [^Class class]
  (or (Modifier/isFinal (.getModifiers class))
      (.isPrimitive class)))

(defn isa [c v]
  (conda [(pred c lvar?)
          (== v c)]
         [(all
            (pred c class?)
            (pred c final?)
            (pred v lvar?)
            (== v c))]
         [(pred c class?)
          (project [c] (predc v #(isa % c) (fn [_ _ r s] `(isa ~(-reify s v r) ~c))))
          (project [c] (fn [a] (add-attr a v ::tag (convert c))))]))

(defn resolve-fn [symbol]
  (some->> symbol source-fn read-string macroexpand-all))

(defn ann-if [ctx test then else type]
  (fresh [then' else']
    (fresh [type] (ann ctx test type))
    (ann ctx then then')
    (ann ctx else else')
    (matche [type] ([then']) ([else']))))

(defn ann-do [ctx exprs type]
  (matcha [exprs]
    ([[]] (== type nil))
    ([[expr]] (ann ctx expr type))
    ([[expr . exprs']]
       (fresh [type] (ann ctx expr type))
       (ann-do ctx exprs' type))))

(defn ann-let [ctx bindings exprs type]
  (matcha [bindings]
    ([[]] (ann-do ctx exprs type))
    ([[var val . bindings']]
       (fresh [ctx' type']
         (conso [var type'] ctx ctx')
         (ann ctx val type')
         (ann-let ctx' bindings' exprs type)))))

(defn tag [symbol type]
  (fresh [tag]
    (is tag symbol (comp :tag meta))
    (pred tag symbol?)
    (is type tag resolve)
    (pred type class?)))

(defna bind [params types bindings]
  ([[] [] []])
  ([['& param] [::seq] [[param ::seq]]])
  ([[param . params'] [type . types'] [[param type] . bindings']]
     (conda [(fresh [class]
               (tag param class)
               (isa class type))]
            [succeed])
     (bind params' types' bindings')))

(defn thunk [ctx name expr ctx']
  (project [expr]
    (conso [name [::thunk ctx expr]] ctx ctx')))

(defn ann-fn
  ([ctx name params exprs type]
     (fresh [ctx']
       (thunk ctx name (llist 'fn* params exprs) ctx')
       (ann-fn ctx' params exprs type)))
  ([ctx params exprs type]
     (matcha [type]
       ([[::fn return . params']]
          (fresh [bindings ctx' ctx'']
            (bind params params' bindings)
            (appendo bindings ctx ctx')
            (conso ['recur type] ctx' ctx'')
            (ann-do ctx'' exprs return))))))

(defn ann-fns
  ([ctx name exprs type]
     (fresh [ctx']
       (thunk ctx name (lcons 'fn* exprs) ctx')
       (ann-fns ctx' exprs type)))
  ([ctx exprs type]
     (matche [exprs]
       ([[[params . body] . _]]
          (ann-fn ctx params body type))
       ([[_ . exprs']]
          (ann-fns ctx exprs' type)))))

(defn ann-list [ctx exprs types]
  (matcha [exprs types]
    ([[] []])
    ([[expr . exprs'] [type . types']]
       (ann ctx expr type)
       (ann-list ctx exprs' types'))))

(defna app [params args]
  ([[] []])
  ([[param] _]
     (pred param (partial = ::seq)))
  ([[param . params'] [arg . args']]
     (isa param arg)
     (app params' args')))

(defn ann-app [ctx exprs type]
  (fresh [types]
    (ann-list ctx exprs types)
    (matcha [types]
      ([[[::fn type . params] . args]] (app params args))
      ([[operator . _]] (pred operator #(isa? % clojure.lang.IFn))))))

(defn loop->fn [expr]
  (let [[_ bindings & exprs] expr
        bindings (partition 2 bindings)]
    `((fn* (~(vec (map first bindings)) ~@exprs)) ~@(map second bindings))))

(defn ann-loop [ctx expr type]
  (project [expr] (ann ctx (loop->fn expr) type)))

(defn resolve-class [symbol type]
  (fresh [var]
    (is var symbol resolve)
    (pred var class?)
    (is type var class)))

(defn ann-var [ctx expr type]
  (matcha [ctx]
    ([[]]
       (fresh [type']
         (conda [(resolve-class expr type)]
                [(project [expr] (ann [] (resolve-fn expr) type'))
                 (matcha [type'] ([[::def expr type]]))])))
    ([[[expr [thunk ctx' expr']] . _]]
       (pred thunk (partial = ::thunk))
       (ann ctx' expr' type))
    ([[[expr type] . _]])
    ([[_ . ctx']]
       (ann-var ctx' expr type))))
  
(defn ann-val [expr type]
  (fresh [var type']
    (conda [(pred expr symbol?)
            (all
             (is var expr reflect/field)
             (pred var (complement nil?))
             (ann [] [] var type))]
           [(is type expr class)])))

(defn constructors [^Class class]
  (map (comp seq (memfn ^Constructor getParameterTypes)) (.getConstructors class)))

(defn ann-new [ctx class args type]
  (fresh [param-types arg-types]
    (pred class symbol?)
    (is type class resolve)
    (pred type class?)
    (project [type] (every param-types (constructors type)))
    (ann-list ctx args arg-types)
    (app param-types arg-types)))

(defn fields [^Class class field]
  (->> class
       .getFields
       (filter #(= (.getName ^Field %) (name field)))
       (map (memfn ^Field getType))))

(defn methods [^Class class method]
  (->> class
       .getMethods
       (filter #(= (.getName ^Method %) (name method)))
       (map #(cons (.getReturnType ^Method %) (.getParameterTypes ^Method %)))))

(defn ann-dot [ctx obj name args type]
  (fresh [class method arg-types]
    (conda [(tag obj class)]
           [(all (pred obj symbol?) (is class obj resolve) (pred class class?))]
           [(fresh [type]
              (ann ctx obj type)
              (conda [(fn [a]
                        (if-let [tag (get-attr a type ::tag)]
                          ((== class tag) a)))]
                     [(is class type convert)])
              (pred class class?))])
    (pred class class?)
    (pred name symbol?)
    (project [class name]
      (conda [(every type (fields class name))]
             [(every method (methods class name))]))
    (matcha [method]
      ([[return . params]]
         (ann-list ctx args arg-types)
         (app params arg-types)
         (isa return type)))))

(defn ann-try [ctx exprs type]
  (fresh [ctx']
    (matcha [ctx'] ([[['catch catch] ['finally finally] . ctx]]))
    (ann-do ctx' exprs type)))

(defn ann-def [ctx name expr type]
  (matcha [type]
    ([[::def name type']]
      (fresh [ctx']
        (thunk ctx name expr ctx')
        (ann ctx' expr type')))))

(defn ann [ctx expr type]
  (matcha [expr]
    ([['def name]]
       (== type [::def name]))
    ([['def name expr']]
       (ann-def ctx name expr' type))
    ([['if test then]]
       (ann-if ctx test then nil type))
    ([['if test then else]]
       (ann-if ctx test then else type))
    ([['do . exprs]]
       (ann-do ctx exprs type))
    ([['let* bindings . exprs]]
       (ann-let ctx bindings exprs type))
    ([['quote expr']]
       (is type expr' class))
    ([['fn* name params . exprs]]
       (pred name symbol?)
       (pred params vector?)
       (ann-fn ctx name params exprs type))
    ([['fn* name . exprs]]
       (pred name symbol?)
       (ann-fns ctx name exprs type))
    ([['fn* params . exprs]]
       (pred params vector?)
       (ann-fn ctx params exprs type))
    ([['fn* . exprs]]
       (ann-fns ctx exprs type))
    ([['loop* . _]]
       (ann-loop ctx expr type))
    ([['try . exprs]]
       (ann-try ctx exprs type))
    ([['throw expr']]
       (fresh [type] (ann ctx expr' type)))
    ([[dot object [method . args]]]
       (== dot '.)
       (ann-dot ctx object method args type))
    ([[dot object method . args]]
       (== dot '.)
       (ann-dot ctx object method args type))
    ([['new object . arguments]]
       (ann-new ctx object arguments type))
    ([_]
       (pred expr seq?)
       (ann-app ctx expr type))
    ([_]
       (pred expr symbol?)
       (ann-var ctx expr type))
    ([_]
       (ann-val expr type))))

(defn check [expr]
  (run *n* [type] (ann [] (macroexpand-all expr) type)))
