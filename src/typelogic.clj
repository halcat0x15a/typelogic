(ns typelogic
  (:require [clojure.string :refer (escape)] 
            [clojure.repl :refer (source-fn)] 
            [clojure.pprint :refer (pprint)]
            [clojure.java.io :refer (resource writer)]
            [typelogic.core :as core])
  (:import clojure.lang.ExceptionInfo))

(def ^:dynamic *filename* ".typelogic.clj")
(def ^:dynamic *timeout* 1000)
(comment
(defn check [symbol]
  (deref (future 
  (try
    (let [result (core/check symbol)]
      (binding [core/*env* core/*env*]
        (doto result prn)))
    (catch Throwable e))) *timeout* nil))

(defn -main [namespace]
  (require (symbol namespace))
  (binding [*ns* (find-ns (symbol namespace))
            core/*env* core/*env*]
    (pprint (->> (ns-map *ns*)
                 (filter (comp var? val))
                 (sort-by #(:line (meta (val %))))
                 (filter #(let [m (meta (val %))] (and (not (:macro m)) (= (:file m) "clojure/core.clj"))))
                 (map (comp check key))
                 doall
                 time)
            (writer *filename*))
    (shutdown-agents)))
)

(defn check [symbol]
  (deref
    (future
      (try
        (binding [core/*env* core/*env*]
          (let [result (core/check symbol)]
            (doto [symbol (doall result)] prn)))
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
