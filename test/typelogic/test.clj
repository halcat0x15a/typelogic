(ns typelogic.test
  (:require [clojure.test :refer :all]
            [clojure.repl :refer (source-fn)]
            [clojure.pprint :refer (pprint)]
            [clojure.java.io :refer (writer)]
            [typelogic.core :refer (*n* check)]))

(deftest type-annotation
  (testing "java interop"
    (are [expr type] (= (set (check expr)) type)
         '(.charAt "" 0) #{Character/TYPE}
         '(StringBuilder. 0) #{StringBuilder})))

#_(deftest clojure-core
  (let [core (the-ns 'clojure.core)
        exprs (->> core
                   ns-publics
                   (sort-by (comp :line meta val))
                   (map (comp source-fn key))
                   (filter identity)
                   (map (comp macroexpand read-string))
                   (filter #(= 'def (first %))))]
    (binding [*ns* core]
      (pprint
       (time (reduce (fn [ctx expr]
                 (try
                   (concat ctx
                         (->> expr
                              (check ctx)
                              distinct
                              (mapcat (fn [type]
                                        (if (and (coll? type) (= (first type) :typelogic.core/var))
                                          [(vec (next type))])))))
                   (catch StackOverflowError _ ctx)))
               (take 250 exprs)))
       (writer "core_type.clj")))))
