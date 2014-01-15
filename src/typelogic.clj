(ns typelogic
  (:require [clojure.string :refer (escape)] 
            [clojure.pprint :refer (pprint)]
            [clojure.java.io :refer (resource writer)]
            [typelogic.core :refer (*n* check)]))

(def filename ".typelogic.clj")

(defn check' [ctx expr]
  (try
    (->> expr
         (check ctx)
         (filter #(= (first %) :typelogic.core/var))
         (map next)
         (concat ctx)
         doall)
    (catch StackOverflowError _ ctx)))

(defn -main [namespace]
  (binding [*ns* (find-ns (symbol namespace))]
    (let [file (-> namespace
                   (escape {\. \/, \- \_})
                   (str ".clj")
                   resource)
          exprs (read-string (str "[" (slurp file) "]"))]
      (pprint (->> exprs
                   (take 100)
                   (reduce check' [])
                   time)
              (writer filename)))))
