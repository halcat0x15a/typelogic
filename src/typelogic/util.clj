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

(defna append* [xs ys zs]
  ([[] _ ys])
  ([[x . xs'] _ [x . zs']]
     (append* xs' ys zs')))

(defmacro append [x y & z]
  (let [vars (vec (repeatedly (dec (count z)) gensym))]
    `(fresh [~@vars]
      ~@(map (fn [[x y z]] `(append* ~x ~y ~z))
             (partition 3 2 (cons y (interleave z (conj vars x))))))))

(defmacro perm [& xs]
  `(conda ~@(map (fn [expr] `[(all ~@expr)]) (permutations xs))))
