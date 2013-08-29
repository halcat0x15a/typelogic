(ns typelogic.test
  (:require [clojure.test :refer :all]
            [typelogic.lisp :refer (check)]))

(deftest type-annotation
  (testing "if"
    (are [expr type] (= (check expr) type)
         '(if true "foo" "bar") #{String}
         '(if true "" 0) #{String Long/TYPE}
         '(if true "") #{String nil}))
  (testing "do"
    (are [expr type] (= (check expr) type)
         '(do "") #{String}
         '(do) #{nil}
         '(do "" 0) #{Long/TYPE}))
  (testing "let"
    (are [expr type] (= (check expr) type)
         '(let [a ""] a) #{String}
         '(let [] 0) #{Long/TYPE}
         '(let [a "" b true] b) #{Boolean}))
  (testing "fn"
    (are [expr type] (= (check expr) type)
         '(fn [] "") #{[:typelogic.lisp/-> [] String]}
         '(fn [a] a) #{'[:typelogic.lisp/-> [_0] _0]}
         '(fn [a b] b) #{'[:typelogic.lisp/-> [_0 _1] _1]}
         '(fn [a] (fn [a] a))
         #{'[:typelogic.lisp/-> [_0] [:typelogic.lisp/-> [_1] _1]]}
         '(fn [^String a] a) #{[:typelogic.lisp/-> [String] String]}
         '(fn [^java.lang.String a] a) #{[:typelogic.lisp/-> [String] String]}
         '(fn [a & x] a) #{[:typelogic.lisp/-> ['_0 clojure.lang.ArraySeq] '_0]}))
  (testing "quote"
    (are [expr type] (= (check expr) type)
         '(quote 0) #{Long/TYPE}
         '(quote (fn [a] a)) #{clojure.lang.LazySeq}))
  (testing "app"
    (are [expr type] (= (check expr) type)
         '((fn [] "")) #{String}
         '((fn [a] a) 0) #{Long/TYPE}
         '((fn [a b] b) 0 true) #{Boolean}
         '((fn [^Object a] a) "") #{Object}
         '((fn [a & x] a) 0 1 2) #{Long/TYPE}
         '((fn [a & x] x) 0 1 2) #{clojure.lang.ArraySeq}))
  (testing "dot"
    (are [expr type] (= (check expr) type)
         '(. clojure.lang.Numbers (inc 0)) #{Long/TYPE}
         '(. clojure.lang.Numbers inc 0) #{Long/TYPE}
         '(. clojure.lang.RT first [""]) #{Object}))
  (testing "new"
    (are [expr type] (= (check expr) type)
         '(new Object) #{Object}
         '(new String "") #{String}))
  (testing "def"
    (is (= (check '(def a "")) #{String})))
  (testing "var"
    (are [expr type] (= (check expr) type)
         'inc #{[:typelogic.lisp/-> [Long/TYPE] Long/TYPE]
                [:typelogic.lisp/-> [Double/TYPE] Double/TYPE]
                [:typelogic.lisp/-> [Object] Number]}
         'first #{[:typelogic.lisp/-> [Object] Object]})))
