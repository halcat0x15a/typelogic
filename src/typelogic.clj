(ns typelogic
  (:require [clojure.string :refer (escape)] 
            [clojure.repl :refer (source-fn)] 
            [clojure.pprint :refer (pprint)]
            [clojure.java.io :refer (resource writer)]
            [typelogic.core :refer (*env* check)])
  (:import clojure.lang.ExceptionInfo))

(def ^:dynamic *filename* ".typelogic.clj")

(defn check' [env expr]
  (try
    (binding [*env* env]
      (prn expr)
      (->> expr
           check
           (mapcat :env)
           (concat env)
           doall))
    (catch StackOverflowError e
      (prn e expr)
      env)
    (catch ExceptionInfo e
      (prn e expr)
      env)))

(defn -main [namespace]
  (binding [*ns* (find-ns (symbol namespace))]
    (let [line (comp :line meta val)
          filename (str (escape namespace {\- \_ \. \/}) ".clj")
          vars (->> *ns*
                     ns-map
                     (filter (comp var? val))
                     (filter (complement (comp :macro meta val)))
                     (sort-by line)
                     (group-by (comp :file meta val))
                     (sort-by #(Math/abs (compare filename (key %))))
                     (mapcat val)
                     (map (comp read-string source-fn key)))]
      (pprint (->> vars
                   (reduce check' [])
                   time)
              (writer *filename*)))))
