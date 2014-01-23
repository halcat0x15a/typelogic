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
    (some->> symbol source-fn read-string check (map (comp second first :env)))))

(defmacro with-ann [env & anns]
  (let [envs (repeatedly (count anns) gensym)]
    `(fresh [~@envs]
       (perm ~@(map (fn [[f & xs] e] `(~f ~e ~@xs)) anns envs))
       (append ~env ~@envs))))

(defn ann-ctx [env ctx expr]
  (fresh [type]
    (ann env ctx expr type)))

(defn ann-if
  ([env ctx exprs type]
     (matcha [exprs]
       ([[test then]]
          (ann-if env ctx test then nil type))
       ([[test then else]]
          (ann-if env ctx test then else type))))
  ([env ctx test then else type]
     (conde [(with-ann env
               (ann-ctx ctx test)
               (ann ctx then type)
               (ann-ctx ctx else))]
            [(with-ann env
               (ann-ctx ctx test)
               (ann-ctx ctx then)
               (ann ctx else type))])))

(defn ann-do [env ctx exprs type]
  (matcha [env exprs type]
    ([[] [] nil])
    ([_ [expr] _] (ann env ctx expr type))
    ([_ [expr . exprs'] _]
       (with-ann env
         (ann-ctx ctx expr)
         (ann-do ctx exprs' type)))))

(defn ann-let
  ([env ctx exprs type]
     (matcha [exprs]
       ([[bindings . exprs']]
          (ann-let env ctx bindings exprs' type))))
  ([env ctx bindings exprs type]
     (matcha [bindings]
       ([[]] (ann-do env ctx exprs type))
       ([[var val . bindings']]
          (fresh [ctx' type']
            (conso [var type'] ctx ctx')
            (with-ann env
              (ann ctx val type')
              (ann-let ctx' bindings' exprs type)))))))

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

(defn ann-fn
  ([env ctx params body type]
     (matcha [type]
       ([[::fn return . types]]
          (fresh [bindings ctx']
            (ann-params params types bindings)
            (append* bindings ctx ctx')
            (ann-do env ctx' body return)))))
  ([env ctx exprs type]
     (matcha [exprs]
       ([[expr . exprs']]
          (conda [(pred expr symbol?)
                  (fresh [ctx']
                    (conso [expr type] ctx ctx')
                    (ann-fn env ctx' exprs' type))]
                 [(pred expr vector?)
                  (ann-fn env ctx expr exprs' type)]
                 [(pred expr seq?)
                  (conde [(ann-fn env ctx expr type)]
                         [(ann-fn env ctx exprs' type)])])))))

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
       (ann-list env ctx operands types))
    ([_]
       (== operator clojure.lang.IFn)
       (fresh [types] (ann-list env ctx operands types)))))

(defna ann-var [ctx expr type]
  ([[[expr type] . ctx'] _ _])
  ([[_ . ctx'] _ _] (ann-var ctx' expr type)))

(defn ann-val [expr type]
  (fresh [var type']
    (conda [(pred expr symbol?)
            (conda [(all
                      (is var expr resolve)
                      (pred var (complement nil?)))
                    (conda [(pred var class?)
                            (== type Class)]
                           [(pred var var?)
                            (project [var]
                              (every type (-> var meta :name resolve-fn)))])]
                   [(all
                      (is var expr reflect/field)
                      (pred var (complement nil?))
                      (ann [] [] var type))])]
           [(is type expr class)])))

(defn call
  ([env ctx exprs type]
     (matcha [exprs]
       ([[obj [method . args]]]
          (call env ctx obj method args type))
       ([[obj method . args]]
          (call env ctx obj method args type))))
  ([env ctx obj name args type]
     (fresh [class method]
       (pred name symbol?)
       (conda [(all
                 (pred obj symbol?)
                 (conda [(tag obj class)]
                        [(is class obj resolve)])
                 (pred class class?)
                 (project [class name]
                   (conda [(every type (reflect/fields class name))
                           (== env [])]
                          [(every method (reflect/methods class name))
                           (app env ctx method args type)])))]
              [(fresh [type']
                 (with-ann env
                   (ann ctx obj type')
                   (app ctx method args type))
                 (is class type' #(if (lvar? %) Object (convert %)))
                 (pred class class?)
                 (project [class name]
                   (conda [(every type (reflect/fields class name)) (== env [])]
                          [(every method (reflect/methods class name))])))]))))
  
(defn construct
  ([env ctx operands type]
     (matcha [operands]
       ([[class . args]]
          (construct env ctx class args type))))
  ([env ctx class args type]
     (fresh [constructor]
       (pred class symbol?)
       (is type class resolve)
       (pred type class?)
       (project [type] (every constructor (reflect/constructors type)))
       (app env ctx constructor args type))))

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
                    (ann-if env ctx operands type)]
                   [(== operator 'do)
                    (ann-do env ctx operands type)]
                   [(== operator 'let*)
                    (ann-let env ctx operands type)]
                   [(== operator 'quote)
                    (matcha [env operands] ([[] [expr']] (is type expr' class)))]
                   [(== operator 'fn*)
                    (ann-fn env ctx operands type)]
                   [(== operator 'loop*)
                    (ann-let env ctx operands type)]
                   [(== operator 'recur)
                    (fresh [types] (ann-list env ctx operands types))]
                   [(== operator 'try)
                    (fresh [ctx' catch finally]
                      (append* [['catch catch] ['finally finally]] ctx ctx')
                      (ann-do env ctx' operands type))]
                   [(== operator 'throw)
                    (matcha [operands] ([[expr']] (ann-ctx env ctx expr')))]
                   [(== operator '.)
                    (call env ctx operands type)]
                   [(== operator 'new)
                    (construct env ctx operands type)]
                   [(pred expr seq?)
                    (fresh [type']
                      (with-ann env
                        (ann ctx operator type')
                        (app ctx type' operands type)))]
                   [(pred expr vector?)
                    (matcha [type]
                      ([[::vec . types]]
                         (ann-list env ctx expr types)))])]
           [(all (pred expr symbol?)
                 (ann-var ctx expr type)
                 (== env []))]
           [(ann-val expr type)
            (== env [])])))

(defn check [expr]
  (distinct
   (run *n* [result]
     (fresh [type env]
       (== result {:type type :env env})
       (ann env [] (macroexpand-all expr) type)))))
