(ns typelogic
  (:require [clojure.pprint :refer [pprint]]
            [clojure.java.io :refer [resource reader writer]]
            [typelogic.core :as core])
  (:import [java.io PushbackReader]))

#_(defn -main [in out & {:strs [debug] :or {"debug" false}}]
  (with-open [r (PushbackReader. (reader (resource in)))
              w (writer out)]
    (let [ctx (atom [])]
      (time
       (doseq [expr (take-while (complement nil?) (repeatedly #(read r false nil)))]
         (if debug (pprint expr))
         (try
           (when-let [[env type] (core/check @ctx expr)]
             (pprint type w)
             (swap! ctx concat (map core/read-env env)))
           (catch RuntimeException e
             (println e))))))))

(defn -main [ns out & {:strs [debug] :or {"debug" false}}]
  (with-open [w (writer out)]
    (binding [*ns* (the-ns (symbol ns))]
      (->> (ns-map *ns*)
           (filter #(and (var? (val %))
                         (not (:macro (meta (val %))))))
           (sort-by (comp :line meta val))
           (map key)
           (reduce (fn [ctx sym]
                     (if debug (pprint sym))
                     (try
                       (if-let [[env type] (core/check ctx sym)]
                         (do
                           (pprint type w)
                           (concat (map core/read-env env)))
                         ctx)
                       (catch RuntimeException e
                         (println e)
                         ctx)))
                   [])
           (dorun)
           (time)))))
