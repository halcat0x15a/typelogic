(ns typelogic.core
  (:refer-clojure :exclude [== isa?])
  (:require [clojure.core :as core]
            [clojure.walk :refer (macroexpand-all)]
            [clojure.repl :refer (source-fn)]
            [clojure.core.logic :refer :all]
            [typelogic.reflect :as reflect]
            [typelogic.util :refer :all]))

(def ^:dynamic *n* 15)
(def ^:dynamic *env* [])

(declare ann)
(declare check)

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
  (cond (keyword? type) (get types type)
        (sequential? type) (get types (first type))
        :else type))

(defn isa? [a b]
  (or (nil? a)
      (and (core/isa? a ::number) (core/isa? b ::number))
      (core/isa? (convert a) (convert b))))

(defn resolve-fn [symbol]
  (if-let [types (->> *env* (filter #(= (first %) symbol)) (map second) seq)]
    types
    (some->> symbol source-fn read-string check (map (comp second second)))))

(defmacro with-ann [env & anns]
  (let [vars (repeatedly (count anns) gensym)]
    `(fresh [~@vars]
       (perm ~@(map (fn [[[f & xs] v]] `(~f ~v ~@xs)) (map vector anns vars)))
       (append ~env ~@vars))))

(defn ann-ctx [env ctx expr]
  (fresh [type]
    (ann env ctx expr type)))

(defn ann-if [env ctx test then else type]
  (conde [(with-ann env
            (ann-ctx ctx test)
            (ann ctx then type)
            (ann-ctx ctx else))]
         [(with-ann env
            (ann-ctx ctx test)
            (ann-ctx ctx then)
            (ann ctx else type))]))

(defn ann-do [env ctx exprs type]
  (matcha [env exprs type]
    ([[] [] nil])
    ([_ [expr] _] (ann env ctx expr type))
    ([_ [expr . exprs'] _]
       (with-ann env
         (ann-ctx ctx expr)
         (ann-do ctx exprs' type)))))

(defn ann-let [env ctx bindings exprs type]
  (matcha [bindings]
    ([[]] (ann-do env ctx exprs type))
    ([[var val . bindings']]
       (fresh [ctx' type']
         (conso [var type'] ctx ctx')
         (with-ann env
           (ann ctx val type')
           (ann-let ctx' bindings' exprs type))))))

(defn tag [symbol type]
  (fresh [tag]
    (is tag symbol (comp :tag meta))
    (pred tag (complement nil?))
    (is type tag reflect/tag->class)))

(defna ann-params [params types bindings]
  ([[] [] []])
  ([['& param] [::seq] [[param ::seq]]])
  ([[param . params'] [type . types'] [[param type] . bindings']]
     (maybe (tag param type))
     (ann-params params' types' bindings')))

(declare ann-fn ann-fns)

(defn ann-fn
  ([env ctx params body type]
     (matcha [type]
       ([[::fn return . types]]
          (fresh [bindings ctx']
            (ann-params params types bindings)
            (appendo bindings ctx ctx')
            (ann-do env ctx' body return)))))
  ([env ctx exprs type]
     (matcha [exprs]
       ([[params . body]]
          (pred params vector?)
          (ann-fn env ctx params body type))
       ([_] (ann-fns env ctx exprs type)))))

(defn ann-fns [env ctx exprs type]
  (matcha [exprs]
    ([[[params . body] . exprs']]
       (conde [(ann-fn env ctx params body type)]
              [(ann-fns env ctx exprs' type)]))))

(defn ann-list [env ctx exprs types]
  (matcha [env exprs types]
    ([[] [] []])
    ([_ [expr . exprs'] [type . types']]
       (fresh [type']
         (with-ann env
           (ann ctx expr type')
           (ann-list ctx exprs' types'))
         (matcha [type']
           ([type])
           ([_] (project [type type'] (== true (isa? type' type)))))))
    ([[] _ [type]]
       (pred type (partial = ::seq)))))

(defn app [env ctx operator operands type]
  (matcha [operator]
    ([[::fn type . types]]
       (ann-list env ctx operands types))))

(defna ann-var [ctx expr type]
  ([[[expr type] . _] _ _])
  ([[_ . ctx'] _ _] (ann-var ctx' expr type)))

(defn ann-val [expr type]
  (fresh [var type']
    (conda [(pred expr symbol?)
            (is var expr resolve)
            (conda [(pred var class?)
                    (== type Class)]
                   [(pred var var?)
                    (project [var]
                      (every type (-> var meta :name resolve-fn)))])]
           [(is type expr class)])))

(defn call [env ctx obj name args type]
  (fresh [class method]
    (pred name symbol?)
    (conda [(all
              (pred obj symbol?)
              (conda [(tag obj class)]
                     [(is class obj resolve)])
              (pred class class?)
              (project [class name]
                (matcha [env]
                  ([[]] (every type (reflect/fields class name)))
                  ([_]
                     (every method (reflect/methods class name))
                     (app env ctx method args type)))))]
           [(with-ann env
              (ann ctx obj class)
              (app ctx method args type))
            (project [class name]
              (let [class' (if (lvar? class) Object class)]
                (conda [(every type (reflect/fields class' name))]
                       [(every method (reflect/methods class' name))])))])))

(defn construct [env ctx class args type]
  (fresh [constructor]
    (pred class symbol?)
    (is type class resolve)
    (pred type class?)
    (project [type] (every constructor (reflect/constructors type)))
    (app env ctx constructor args type)))

(defn ann [env ctx expr type]
  (fresh [operator operands]
    (conda [(conso operator operands expr)
            (conda [(== operator 'def)
                    (matcha [env operands type]
                      ([[[name type']] [name] [::var name type']])
                      ([[[name type'] . env'] [name expr'] [::var name type']]
                         (fresh [ctx']
                           (conso [name type'] ctx ctx')
                           (ann env' ctx' expr' type'))))]
                   [(== operator 'deftype*)
                    (matcha [env type] ([[] nil]))]
                   [(== operator 'if)
                    (matcha [operands]
                      ([[test then]]
                         (ann-if env ctx test then nil type))
                      ([[test then else]]
                         (ann-if env ctx test then else type)))]
                   [(== operator 'do)
                    (ann-do env ctx operands type)]
                   [(== operator 'let*)
                    (matcha [operands]
                      ([[bindings . exprs]]
                         (ann-let env ctx bindings exprs type)))]
                   [(== operator 'quote)
                    (matcha [env operands]
                      ([[] [expr']]
                         (is type expr' class)))]
                   [(== operator 'fn*)
                    (matcha [operands]
                      ([[name . exprs]]
                         (fresh [ctx']
                           (pred name symbol?)
                           (conso [name type] ctx ctx')
                           (ann-fn env ctx' exprs type)))
                      ([_] (ann-fn env ctx operands type)))]
                   [(== operator 'loop*)
                    (matcha [operands]
                      ([[bindings . exprs]]
                         (ann-let env ctx bindings exprs type)))]
                   [(== operator 'recur)
                    (fresh [types] (ann-list env ctx operands types))]
                   [(== operator 'try)
                    (fresh [ctx' catch finally]
                      (appendo [['catch catch] ['finally finally]] ctx ctx')
                      (ann-do env ctx' operands type))]
                   [(== operator 'throw)
                    (matcha [operands]
                      ([[expr']] (ann-ctx env ctx expr')))]
                   [(== operator '.)
                    (matcha [operands]
                      ([[obj [method . args]]]
                         (call env ctx obj method args type))
                      ([[obj method . args]]
                         (call env ctx obj method args type)))]
                   [(== operator 'new)
                    (matcha [operands]
                      ([[class . args]]
                         (construct env ctx class args type)))]
                   [(pred expr seq?)
                    (fresh [type']
                      (with-ann env
                        (ann ctx operator type')
                        (app ctx type' operands type)))]
                   [(pred expr vector?)
                    (matcha [type]
                      ([[::vec . types]]
                         (ann-list env ctx expr types)))])]
           [(matcha [env]
              ([[]]
                 (conda [(all (pred expr symbol?)
                              (ann-var ctx expr type))]
                        [(ann-val expr type)])))])))

(defn check [expr]
  (distinct
   (run *n* [result]
     (fresh [type env]
       (conso type env result)
       (ann env [] (macroexpand-all expr) type)))))
