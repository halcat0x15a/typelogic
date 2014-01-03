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

(defn methods [^Class class method]
  (->> class
       .getMethods
       (filter #(= (.getName ^Method %) (name method)))
       (map #(apply vector (.getReturnType ^Method %) (.getParameterTypes ^Method %)))))

(defn fields [^Class class field]
  (->> class
       .getFields
       (filter #(= (.getName ^Field %) (name field)))
       (map (memfn ^Field getType))))

(defn constructors [^Class class]
  (->> class
       .getConstructors
       (map #(apply vector class (.getParameterTypes ^Constructor %)))))

(defn supers [class]
  (loop [^Class class class
         supers []]
    (if (or (nil? class) (= class Object))
      (conj supers Object)
      (recur (.getSuperclass class) (into (conj supers class) (.getInterfaces class))))))

(def numbers
  [Long/TYPE Integer/TYPE Double/TYPE Float/TYPE
   Long Integer Double Float])

(defn infer [x]
  (try
    (let [expr (Compiler/analyze clojure.lang.Compiler$C/STATEMENT x)
          type (class expr)]
      (if (some-> type (method 'hasJavaClass) (invoke expr) boolean)
        (-> type (method 'getJavaClass) (invoke expr))))
    (catch RuntimeException _)))
