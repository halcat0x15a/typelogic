(ns typelogic.test
  (:require [clojure.test :refer :all]
            [typelogic.lisp :refer (check)]))

(deftest type-annotation
  (testing "if"
    (are [x y] (= x y)
         (check '(if true "foo" "bar")) String
         (check '(if true "" 0)) [:typelogic.lisp/+ Long String]
         (check '(if true "")) [:typelogic.lisp/+ nil String]))
  (testing "do"
    (are [x y] (= x y)
         (check '(do "")) String
         (check '(do)) nil
         (check '(do "" 0)) Long))
  (testing "let"
    (are [x y] (= x y)
         (check '(let [a ""] a)) String
         (check '(let [] 0)) Long
         (check '(let [a "" b true] b)) Boolean))
  (testing "fn"
    (are [x y] (= x y)
         (check '(fn [] "")) [:typelogic.lisp/-> [] String]
         (check '(fn [a] a)) '[:typelogic.lisp/-> [_0] _0]
         (check '(fn [a b] b)) '[:typelogic.lisp/-> [_0 _1] _1]
         (check '(fn [a] (fn [a] a)))
         '[:typelogic.lisp/-> [_0] [:typelogic.lisp/-> [_1] _1]]
         (check '(fn [^String a] a)) [:typelogic.lisp/-> [String] String]))
  (testing "app"
    (are [x y] (= x y)
         (check '((fn [] ""))) String
         (check '((fn [a] a) 0)) Long
         (check '((fn [a b] b) 0 true)) Boolean)))
