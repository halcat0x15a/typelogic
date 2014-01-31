(ns typelogic
  (:require [clojure.string :refer (escape)] 
            [clojure.repl :refer (source-fn)] 
            [clojure.pprint :refer (pprint)]
            [clojure.java.io :refer (resource writer)]
            [typelogic.core :refer (*env*) :as core])
  (:import clojure.lang.ExceptionInfo))

(def ^:dynamic *filename* ".typelogic.clj")
(def ^:dynamic *timeout* 60000)

(defn check [env symbol]
  (-> (try
        (binding [*env* env]
          (prn symbol)
          (->> symbol
               source-fn
               read-string
               core/check
               (mapcat :env)
               (concat env)
               doall))
        (catch StackOverflowError e
          (prn e symbol)
          env)
        (catch ExceptionInfo e
          (prn e symbol)
          env))
      future
      (deref *timeout* env)))

(defn -main [namespace]
  (binding [*ns* (find-ns (symbol namespace))]
    (pprint (->> *ns*
                 ns-map
                 (filter (comp var? val))
                 (filter (complement (comp :macro meta val)))
                 (sort-by (comp :line meta val))
                 (group-by (comp :file meta val))
                 (filter #(= (str (escape namespace {\- \_ \. \/}) ".clj") (key %)))
                 (mapcat val)
                 (map key)
                 (reduce check [])
                 time)
            (writer *filename*))
    (shutdown-agents)))
