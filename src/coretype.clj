(ns coretype
  (:require [clojure.repl :refer (source-fn)]
            [clojure.pprint :refer (pprint)]
            [clojure.java.io :refer (writer)]
            [typelogic.core :refer (*n* check)]))

(def core (the-ns 'clojure.core))

(def exprs
  (->> core
       ns-publics
       (filter #(= (:file (meta (val %))) "clojure/core.clj"))
       (sort-by (comp :line meta val))
       (map (comp source-fn key))
       (filter identity)
       (map (comp macroexpand read-string))
       (filter #(= 'def (first %)))))

(defn context [ctx expr]
  (try
    (->> expr
         (check ctx)
         distinct
         (mapcat (fn [type]
                   (if (and (coll? type) (= (first type) :typelogic.core/var))
                     [(vec (next type))])))
         (concat ctx))
    (catch StackOverflowError _ ctx)))

(defn -main []
  (binding [*ns* core]
    (pprint (->> exprs
                 (take 100)
                 (reduce context)
                 time)
            (writer "types.clj"))))
