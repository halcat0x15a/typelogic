(ns typelogic.test
  (:require [clojure.test :refer :all]
            [typelogic.lisp :refer (check)]))

(deftest type-annotation
  (testing "if"
    (are [expr type] (= (second (check expr)) type)
         '(if true "foo" "bar") String
         '(if true "" 0) [:typelogic.lisp/+ Long String]
         '(if true "") [:typelogic.lisp/+ nil String]))
  (testing "do"
    (are [expr type] (= (second (check expr)) type)
         '(do "") String
         '(do) nil
         '(do "" 0) Long))
  (testing "let"
    (are [expr type] (= (second (check expr)) type)
         '(let [a ""] a) String
         '(let [] 0) Long
         '(let [a "" b true] b) Boolean))
  (testing "fn"
    (are [expr type] (= (second (check expr)) type)
         '(fn [] "") [:typelogic.lisp/-> [] String]
         '(fn [a] a) '[:typelogic.lisp/-> [_0] _0]
         '(fn [a b] b) '[:typelogic.lisp/-> [_0 _1] _1]
         '(fn [a] (fn [a] a))
         '[:typelogic.lisp/-> [_0] [:typelogic.lisp/-> [_1] _1]]
         '(fn [^String a] a) [:typelogic.lisp/-> [String] String]
         '(fn [^java.lang.String a] a) [:typelogic.lisp/-> [String] String]))
  (testing "app"
    (are [expr type] (= (second (check expr)) type)
         '((fn [] "")) String
         '((fn [a] a) 0) Long
         '((fn [a b] b) 0 true) Boolean))
  (testing "def"
    (is (= (first (check '(def a ""))) [['a String]]))))
