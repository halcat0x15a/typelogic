(ns typelogic.clojure
  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic :refer (run)]
            [clojure.repl :refer (source-fn)]
            [clojure.walk :refer (macroexpand-all)]
            [typelogic.core :refer (check-all)]))

(def core (the-ns 'clojure.core))

(def sources
  (binding [*ns* core]
    (->> core
         ns-publics
         (sort-by (comp :line meta val))
         (map (comp source-fn key))
         (filter identity)
         (map (comp macroexpand-all read-string))
         (filter #(= 'def (first %)))
         doall)))

(defn -main
  ([] (-main sources))
  ([exprs]
     (first (run 1 [q] (check-all [] exprs q)))))

  (binding [*ns* core]
(doseq [var (time (-main (take 50 sources)))] (prn var)))
