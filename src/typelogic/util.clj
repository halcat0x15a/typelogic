(ns typelogic.util
  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic :refer :all]
            [clojure.math.combinatorics :refer (permutations)]))

(defn maybe [x]
  (conda [x] [succeed]))

(defne every [x xs]
  ([_ [x . _]])
  ([_ [_ . xs']]
     (every x xs')))

(defmacro append [x y & z]
  (let [vars (vec (repeatedly (dec (count z)) gensym))]
    `(fresh [~@vars]
      ~@(map (fn [[x y z]] `(appendo ~x ~y ~z))
             (partition 3 2 (cons y (interleave z (conj vars x))))))))

(defmacro perm [& xs]
  `(conda ~@(map (fn [expr] `[(all ~@expr)]) (permutations xs))))
