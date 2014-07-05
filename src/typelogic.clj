(ns typelogic
  (:require [clojure.string :refer (escape)] 
            [clojure.repl :refer (source-fn)] 
            [clojure.pprint :refer (pprint)]
            [clojure.java.io :refer (resource writer)]
            [typelogic.core :as core])
  (:import clojure.lang.ExceptionInfo))

(def ^:dynamic *filename* ".typelogic.clj")
(def ^:dynamic *timeout* 1000)

(defn check [symbol]
  (deref
    (future
      (try
        (let [result (core/check symbol)]
          (doto (doall result) prn))
        (catch Throwable e)))
      *timeout*
      nil))

(defn -main [namespace]
  (require (symbol namespace))
  (binding [*ns* (find-ns (symbol namespace))]
    (pprint (->> (ns-map *ns*)
                 (filter (comp var? val))
                 (filter (complement (comp :macro meta val)))
                 (map key)
                 (pmap check)
                 (reduce concat [])
                 time)
            (writer *filename*))
    (shutdown-agents)))
