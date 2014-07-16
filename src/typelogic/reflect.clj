(ns typelogic.reflect
  (:refer-clojure :exclude [supers methods isa?])
  (:require [clojure.core :as core])
  (:import [java.lang.reflect Modifier Method Field Constructor]))

(defn final? [^Class class]
  (and (class? class)
       (or (Modifier/isFinal (.getModifiers class))
           (.isPrimitive class))))

(defn constructors [^Class class]
  (map #(seq (.getParameterTypes ^Constructor %)) (.getConstructors class)))

(defn methods [^Class class method]
  (->> (.getMethods class)
       (filter #(= (.getName ^Method %) (name method)))
       (map #(fn [^Method m] (cons (.getReturnType m) (.getParameterTypes m))))))

(defn field [^Class class field]
  (try
    (.getField class (name field))
    (catch NoSuchFieldException _)))

(defn tag->class [tag]
  (get primitives tag (resolve tag)))

(defn methods [^Class class method]
  (->> class
       .getDeclaredMethods
       (filter #(= (.getName ^Method %) (name method)))
       (map #(cons (.getReturnType ^Method %) (.getParameterTypes ^Method %)))
       reverse))

(defn fields [^Class class field]
  (->> class
       .getFields
       (filter #(= (.getName ^Field %) (name field)))
       (map (memfn ^Field getType))))

(defn static-field [sym]
  (let [[_ class field] (re-matches #"(.+?)/(.+)" (str sym))]
    (if (and class field)
      [(symbol class) (symbol field)])))

(def primitives
  {'long Long/TYPE
   'double Double/TYPE})

(defn tag [sym]
  (if-let [tag (some-> sym meta :tag)]
    (if-let [class (primitives tag)]
      class
      (if-let [var (resolve tag)]
        (if (class? var)
          var)))))
