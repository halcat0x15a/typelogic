(ns typelogic.test
  (:require [clojure.test :refer :all]
            [typelogic.core :refer (check)]))

(deftest type-annotation
  (testing "if"
    (are [expr type] (= (set (check expr)) type)
         '(if true 0 0) #{Long}
         '(if true 0 "") #{Long String}
         '(if true 0) #{Long nil}))
  (testing "do"
    (are [expr type] (= (set (check expr)) type)
         '(do 0 "") #{String}
         '(do) #{nil}))
  (testing "let"
    (are [expr type] (= (set (check expr)) type)
         '(let [a 0] a) #{Long}))
  (testing "fn"
    (are [expr type] (= (set (check expr)) type)
         '(fn [a] a) #{'(::typelogic.core/fn _0 _0)}
         '(fn [^String a] a) #{'(::typelogic.core/fn _0 _0)}))
  (testing "java interop"
    (are [expr type] (= (set (check expr)) type)
         '(.charAt "" 0) #{Character/TYPE}
         '(StringBuilder. 0) #{StringBuilder})))
