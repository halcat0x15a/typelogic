(ns leiningen.typecheck
  (:require [clojure.java.io :refer (file)]
            [clojure.string :as string]
            [typelogic.lisp :refer (check)]))

(defn typecheck
  ([project] (apply typecheck project (:source-paths project)))
  ([project & sources]
     (doseq [source sources
             file (->> source file file-seq
                       (filter #(and (.isFile %) (.endsWith (.getName %) ".clj"))))]
       (let [path (.getPath file)]
         (-> path
             (subs (inc (count source)) (- (count path) 4))
             (string/replace #"/" ".")
             symbol
             (doto prn)
             in-ns)
         (as-> file %
               (slurp %)
               (str "[" % "]")
               (read-string %)
               (pmap (fn [expr]
                       (try
                         (prn (check expr))
                         (catch Throwable e (prn e))))
                     %)
               (dorun %))))))
