(ns typelogic.core
  (:refer-clojure :exclude [== record?])
  (:require [clojure.core :as core]
            [clojure.walk :refer [macroexpand-all]]
            [clojure.repl :refer [source-fn]]
            [clojure.core.logic :refer :all]
            [clojure.core.logic.pldb :as pldb]
            [clojure.core.logic.protocols :refer [lfirst]]
            [typelogic.reflect :as reflect]))

(def ^:dynamic *n* 15)

(def ^:dynamic *env* pldb/empty-db)

(pldb/db-rel global sym type)

(declare ann)

(defmulti convert
  (fn [type]
    (cond (class? type) ::class
          (sequential? type) (first type)
          (lcons? type) (lfirst type)
          (lvar? type) ::lvar
          (nil? type) ::nil)))

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
(defmethod convert ::class [type] type)
(defmethod convert ::lvar [_] Object)
(defmethod convert ::nil [_] nil)
(defmethod convert :default [_] Object)

(defn subtype? [a b]
  (or (and (isa? b Object) (nil? a))
      (and (isa? (convert a) Number) (isa? (convert b) Number))
      (isa? (convert a) (convert b))))

(defn subtype [a b]
  (conda [(all (pred b reflect/final?) (== a b))]
         [(== a b)]
         [(all
           (pred b class?)
           (project [b]
                    (predc a #(subtype? % b) (fn [_ _ r s] (list 'subtype (-reify s a r) b)))))]))

(defn resolve-fn [symbol]
  (some->> symbol source-fn read-string macroexpand-all))

(defn ann-if [ctx test then else type]
  (fresh [then' else']
    (fresh [type] (ann ctx test type))
    (ann ctx then then')
    (ann ctx else else')
    (condu [(all (== type then') (== type else'))]
           [(conde [(== type then')] [(== type else')])])))

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
         (ann ctx val type')
         (conso [var type'] ctx ctx')
         (ann-let ctx' bindings' exprs type)))))

(defn tag [symbol type]
  (fresh [tag]
    (is tag symbol (comp :tag meta))
    (pred tag symbol?)
    (is type tag resolve)
    (pred type class?)))

(defna make-bindings [syms params bindings]
  ([[] [] []])
  ([['& sym] [[:seq]] [[sym [:seq]]]])
  ([[sym . syms'] [param . params'] [[sym param] . bindings']]
     (conda [(tag sym param)]
            [succeed])
     (make-bindings syms' params' bindings')))

(defn ann-fn [ctx syms exprs type]
  (fresh [bindings ctx']
    (pred syms vector?)
    (matcha [bindings type]
      ([[['recur type] . bindings'] [:fn params return]]
         (make-bindings syms params bindings')
         (appendo bindings ctx ctx')
         (ann-do ctx' exprs return)))))

(defn ann-fns [ctx exprs type]
  (matche [exprs]
    ([[[syms . body] . _]]
       (ann-fn ctx syms body type))
    ([[_ . exprs']]
       (ann-fns ctx exprs' type))))

(defn ann-named-fn [ctx name syms exprs type]
  (fresh [ctx']
    (pred name symbol?)
    (conso [name type] ctx ctx')
    (ann-fn ctx' syms exprs type)))

(defn ann-named-fns [ctx name exprs type]
  (fresh [ctx' type']
    (pred name symbol?)
    (conso [name type'] ctx ctx')
    (ann-fns ctx' exprs type)
    (condu [(ann-fns ctx exprs type')])))

(defn ann-list [ctx exprs types]
  (matcha [exprs types]
    ([[] []])
    ([[expr . exprs'] [type . types']]
       (ann ctx expr type)
       (ann-list ctx exprs' types'))))

(defna app [params args]
  ([[] []])
  ([[param . params'] [arg . args']]
     (subtype arg param)
     (app params' args'))
  ([[[param]] _] (pred param #(= % :seq))))

(defn ann-app [ctx exprs type]
  (fresh [types]
    (ann-list ctx exprs types)
    (matcha [types]
      ([[[:fn params type] . args]]
         (app params args))
      ([[[:var name [:fn params type]] . args]]
         (app params args)))))

(defn ann-loop [ctx expr type]
  (letfn [(loop->fn [expr]
            (let [[_ bindings & exprs] expr
                  bindings (partition 2 bindings)]
              `((fn* (~(vec (map first bindings)) ~@exprs))
                ~@(map second bindings))))]
    (project [expr] (ann ctx (loop->fn expr) type))))

(defn resolve-class [symbol type]
  (all
    (is type symbol resolve)
    (pred type class?)))

(defn ann-global [expr type]
  (conda [(fresh [type]
            (resolve-class expr type))
            (== type java.lang.Class)]
         [(project [expr]
            (ann [] (resolve-fn expr) type))]))

(defn ann-var [ctx expr type]
  (matcha [ctx]
    ([[[expr type] . _]])
    ([[_ . ctx']]
       (ann-var ctx' expr type))))
  
(defn ann-val [expr type]
  (fresh [var type']
    (conda [(pred expr symbol?)
            (all
             (is var expr reflect/static-field)
             (pred var (complement nil?))
             (ann [] [] var type))]
           [(is type expr class)])))

(defn overload [fn fns]
  (matche [fns]
    ([[fn . _]])
    ([[_ . fns']]
       (overload fn fns'))))

(defn ann-new [ctx class exprs type]
  (fresh [params args]
    (pred class symbol?)
    (is type class resolve)
    (pred type class?)
    (project [type] (overload params (reflect/constructors type)))
    (ann-list ctx exprs args)
    (app params args)))

(defn ann-receiver [ctx expr class]
  (conda [(tag expr class)]
         [(resolve-class expr class)]
         [(fresh [type]
            (ann ctx expr type)
            (is class type convert)
            (pred class class?))]))

(defn ann-field [ctx expr field type]
  (fresh [class]
    (pred field symbol?)
    (ann-receiver ctx expr class)
    (project [field]
      (is type class #(reflect/field % field)))
    (pred type class?)))

(defn ann-method [ctx expr name exprs type]
  (fresh [class method args]
    (pred name symbol?)
    (ann-receiver ctx expr class)
    (project [class name]
      (overload method (reflect/methods class name)))
    (ann-list ctx exprs args)
    (matcha [method]
      ([[return . params]]
         (app params args)
         (subtype type return)))))

(defn ann-try [ctx exprs type]
  (fresh [ctx']
    (matcha [ctx'] ([[['catch catch] ['finally finally] . ctx]]))
    (ann-do ctx' exprs type)))

(defn ann-def [ctx name expr var]
  (fresh [ctx' type']
    (matcha [var]
      ([[:var name type]]
         (conso [name type'] ctx ctx')
         (ann ctx' expr type)
         (condu [(ann ctx expr type')])
         (project [name type]
           (do
             (set! *env* (pldb/db-fact *env* global name type))
             succeed))))))

(defn ann [ctx expr type']
  (fresh [type]
    (matcha [expr]
      ([['def name]]
         (== type [:var name]))
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
      ([['fn* name syms . exprs]]
         (ann-named-fn ctx name syms exprs type))
      ([['fn* name . exprs]]
         (ann-named-fns ctx name exprs type))
      ([['fn* syms . exprs]]
         (ann-fn ctx syms exprs type))
      ([['fn* . exprs]]
         (ann-fns ctx exprs type))
      ([['loop* . _]]
         (ann-loop ctx expr type))
      ([['try . exprs]]
         (ann-try ctx exprs type))
      ([['throw expr']]
         (fresh [type] (ann ctx expr' type)))
      ([[dot expr' field]]
         (== dot '.)
         (ann-field ctx expr' field type))
      ([[dot expr' [method . args]]]
         (== dot '.)
         (ann-method ctx expr' method args type))
      ([[dot expr' method . args]]
         (== dot '.)
         (ann-method ctx expr' method args type))
      ([['new class . args]]
         (ann-new ctx class args type))
      ([_]
         (pred expr seq?)
         (ann-app ctx expr type))
      ([_]
         (pred expr symbol?)
         (conda [(ann-var ctx expr type)]
                [(global expr type)]
                [(ann-global expr type)]))
      ([_]
         (ann-val expr type)))
    (subtype type' type)))

(defn check [expr]
  (doall
   (pldb/with-db *env*
     (run *n* [type]
       (ann [] (macroexpand-all expr) type)))))
