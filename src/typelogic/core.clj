(ns typelogic.core
  (:refer-clojure :exclude [==])
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

(derive Byte/TYPE ::number)
(derive Byte ::number)
(derive Short/TYPE ::number)
(derive Short ::number)
(derive Integer/TYPE ::number)
(derive Integer ::number)
(derive Long/TYPE ::number)
(derive Long ::number)
(derive Float/TYPE ::number)
(derive Float ::number)
(derive Double/TYPE ::number)
(derive Double ::number)

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
  (get (merge primitives literals)
       (if (sequential? type) (first type) type)
       type))

(defn isa [v c]
  (project [c]
    (predc v #(or (nil? %) (and (isa? % ::number) (isa? c ::number)) (isa? (convert %) (convert c))) (fn [_ v _ _] `(isa ~v ~c)))))

(defn resolve-fn [symbol]
  (if-let [types (->> *env* (filter #(= (first %) symbol)) (map second) seq)]
    types
    (some->> symbol source-fn read-string check (map (comp second first :env)))))

(defmacro with-ann [env & anns]
  (let [envs (repeatedly (count anns) gensym)]
    `(fresh [~@envs]
       ~@(map (fn [[f & xs] e] `(~f ~e ~@xs)) anns envs)
       (append ~env ~@envs))))

(defn ann-ctx [env ctx expr]
  (fresh [type] (ann env ctx expr type)))

(defn ann-if
  ([env ctx exprs type]
     (matcha [exprs]
       ([[test then]]
          (ann-if env ctx test then nil type))
       ([[test then else]]
          (ann-if env ctx test then else type))))
  ([env ctx test then else type]
     (fresh [then' else']
       (with-ann env
         (ann-ctx ctx test)
         (ann ctx then then')
         (ann ctx else else'))
       (conda [(all (== type then') (== type else'))]
              [(matche [type] ([then']) ([else']))]))))

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
  ([env ctx exprs type]
     (fresh [ctx' return params]
       (matcha [type] ([[::fn return . params]]))
       (matcha [ctx' exprs]
         ([[[name [::delay exprs]] ['recur type] . ctx] [name . exprs']]
            (pred name symbol?)
            (ann-fn env ctx' exprs' return params))
         ([[['recur type] . ctx] _]
            (ann-fn env ctx' exprs return params)))))
  ([env ctx exprs return params]
     (matcha [exprs]
       ([[expr . exprs']]
          (pred expr vector?)
          (fresh [bindings ctx']
            (ann-params expr params bindings)
            (append* bindings ctx ctx')
            (ann-do env ctx' exprs' return)))
       ([[expr . exprs']]
          (pred expr seq?)
          (conde [(ann-fn env ctx expr return params)]
                 [(ann-fn env ctx exprs' return params)])))))

(defn ann-list [env ctx exprs types]
  (matcha [env exprs types]
    ([[] [] []])
    ([_ [expr . exprs'] [type . types']]
       (with-ann env
         (ann ctx expr type)
         (ann-list ctx exprs' types')))))

(defn ann-app
  ([env ctx exprs type]
     (fresh [types]
       (ann-list env ctx exprs types)
       (matcha [types]
         ([[operators . oprands]] (ann-app operators oprands type)))))
  ([operators operands type]
     (matcha [operators]
       ([[::fn type . params]] (ann-app params operands))
       ([_] (equals operators clojure.lang.IFn))))
  ([params args]
     (matcha [params args]
       ([[] []])
       ([[type . types] [type . types']] (ann-app types types'))
       ([[type . types] [type' . types']]
          (isa type' type)
          (ann-app types types'))
       ([[type] _] (equals type ::seq)))))

(defn ann-loop
  ([env ctx exprs type]
     (matcha [exprs]
       ([[bindings . exprs']]
          (fresh [expr params args]
            (ann-loop bindings params args)
            (matcha [expr] ([[['fn* [params' . exprs']] . args]] (is params' params vec)))
            (ann-app env ctx expr type)))))
  ([bindings params args]
     (matcha [bindings params args]
       ([[] [] []])
       ([[param arg . bindings'] [param . params'] [arg . args']]
          (ann-loop bindings' params' args')))))

(defna ann-var [env ctx expr type]
  ([_ [[expr [::delay expr']] . _] _ _]
     (condu [(ann-fn env ctx expr' type)]))
  ([[] [[expr type] . _] _ _])
  ([_ [_ . ctx'] _ _] (ann-var env ctx' expr type)))

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

(defn ann-obj [env ctx obj class]
  (matcha [env]
    ([[]]
       (pred obj symbol?)
       (conda [(tag obj class)]
              [(is class obj resolve)])
       (pred class class?))
    ([_]
       (fresh [type]
         (ann env ctx obj type)
         (maybe (== type Object))
         (is class type convert)
         (pred class class?)))))

(defn ann-dot
  ([env ctx exprs type]
     (matcha [exprs]
       ([[obj [name . args]]]
          (ann-dot env ctx obj name args type))
       ([[obj name . args]]
          (ann-dot env ctx obj name args type))))
  ([env ctx obj name args type]
     (fresh [class types]
       (pred name symbol?)
       (with-ann env
         (ann-obj ctx obj class)
         (ann-list ctx args types))
       (project [class name]
         (conda [(every type (reflect/fields class name))]
                [(fresh [method]
                   (every method (map (partial cons ::fn) (reflect/methods class name)))
                   (ann-app method types type))])))))
  
(defn ann-new [env ctx exprs type]
  (fresh [class args constructor types]
    (conso class args exprs)
    (pred class symbol?)
    (is type class resolve)
    (pred type class?)
    (project [type]
      (every constructor (map (partial cons ::fn) (reflect/constructors type))))
    (ann-list env ctx args types)
    (ann-app constructor types type)))

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
                    (ann-loop env ctx operands type)]
                   [(== operator 'try)
                    (fresh [ctx']
                      (matcha [ctx'] ([[['catch catch] ['finally finally] . ctx]]))
                      (ann-do env ctx' operands type))]
                   [(== operator 'throw)
                    (matcha [operands] ([[expr']] (ann-ctx env ctx expr')))]
                   [(== operator '.)
                    (ann-dot env ctx operands type)]
                   [(== operator 'new)
                    (ann-new env ctx operands type)]
                   [(pred expr seq?)
                    (ann-app env ctx expr type)]
                   [(pred expr vector?)
                    (matcha [type]
                      ([[::vec . types]] (ann-list env ctx expr types)))])]
           [(all (pred expr symbol?)
                 (ann-var env ctx expr type))]
           [(ann-val expr type)
            (== env [])])))

(defn check [expr]
  (run *n* [result]
    (fresh [type env]
      (== result {:type type :env env})
      (ann env [] (macroexpand-all expr) type))))
