(ns typelogic.test
  (:require [clojure.test :refer :all]
            [clojure.repl :refer (source-fn)]
            [typelogic.core :refer (check check-all')]))

(deftest type-annotation
  (testing "java interop"
    (are [expr type] (= (set (check expr)) type)
         '(.charAt "" 0) #{Character/TYPE}
         '(StringBuilder. 0) #{StringBuilder})))

(deftest clojure-core
  (let [core (the-ns 'clojure.core)
        exprs (->> core
                     ns-publics
                     (sort-by (comp :line meta val))
                     (map (comp source-fn key))
                     (filter identity)
                     (map read-string)
                     (filter #(= 'def (first %))))]
    (binding [*ns* core]
      (doseq [var (check-all' (take 50 exprs))]
        (prn var)))))
