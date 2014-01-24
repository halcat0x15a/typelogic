(ns typelogic.test
  (:require [clojure.test :refer :all]
            [typelogic.core :refer (check)]))

(deftest type-annotation
  (testing "java interop"
    (are [expr type] (= (set (map :type (check expr))) type)
         '(.charAt "" 0) #{Character/TYPE}
         '(StringBuilder. 0) #{StringBuilder})))
