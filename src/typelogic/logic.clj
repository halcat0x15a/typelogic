(ns typelogic.logic
  (:refer-clojure :exclude [== map])
  (:require [clojure.core.logic :refer :all]))

(defn map [f xs ys]
  (matcha [xs ys]
    ([[] []])
    ([[x . xs'] [y . ys']]
      (f x y)
      (map f xs' ys'))))

(defn any [x xs]
  (matche [xs]
    ([[x . _]])
    ([[_ . xs']]
      (any x xs'))))
