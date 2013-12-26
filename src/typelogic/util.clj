(ns typelogic.util
  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic :refer :all]))

(defne every [x xs]
  ([_ [x . _]])
  ([_ [_ . xs']]
     (every x xs')))

(defna zip [xs ys zs]
  ([[] [] []])
  ([[x . xs'] [y . ys'] [[x y] . zs']]
     (zip xs' ys' zs')))
