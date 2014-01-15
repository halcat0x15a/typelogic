(ns typelogic.reflect
  (:refer-clojure :exclude [supers methods isa?])
  (:require [clojure.core :as core])
  (:import [java.lang.reflect Method Field Constructor]))

(defn method [^Class class method & parameter-types]
  (try
    (doto (.getDeclaredMethod class (name method) (into-array Class parameter-types))
      (.setAccessible true))
    (catch NoSuchMethodException _)))

(defn invoke [^Method method obj & args]
  (.invoke method obj  (into-array Object args)))

(defn tag->class [tag]
  (-> clojure.lang.Compiler$HostExpr
      (method 'tagToClass Object)
      (invoke nil tag)))

(defn symbol->class [class]
  (-> clojure.lang.Compiler$HostExpr
      (method 'maybeClass Object Boolean/TYPE)
      (invoke nil class true)))

(defn function [return params]
  (apply vector :typelogic.core/fn return params))

(defn methods [^Class class method]
  (->> class
       .getMethods
       (filter #(= (.getName ^Method %) (name method)))
       (map #(function (.getReturnType ^Method %) (.getParameterTypes ^Method %)))))

(defn fields [^Class class field]
  (->> class
       .getFields
       (filter #(= (.getName ^Field %) (name field)))
       (map (memfn ^Field getType))))

(defn constructors [^Class class]
  (->> class
       .getConstructors
       (map #(function class (.getParameterTypes ^Constructor %)))))

(defn infer [x]
  (try
    (let [expr (Compiler/analyze clojure.lang.Compiler$C/STATEMENT x)
          type (class expr)]
      (if (some-> type (method 'hasJavaClass) (invoke expr) boolean)
        (-> type (method 'getJavaClass) (invoke expr))))
    (catch RuntimeException _)))

