(ns typelogic.reflect
  (:refer-clojure :exclude [supers methods isa?])
  (:require [clojure.core :as core])
  (:import [java.lang.reflect Modifier Method Field Constructor]))

(defn final? [^Class class]
  (and (class? class)
       (or (Modifier/isFinal (.getModifiers class))
           (.isPrimitive class))))

(defn constructors [^Class class]
  (map #(seq (.getParameterTypes ^Constructor %))
       (.getConstructors class)))

(defn methods [^Class class method]
  (->> (.getMethods (get box class class))
       (filter #(= (.getName ^Method %) (name method)))
       (map (fn [^Method m] [(vec (.getParameterTypes m)) (.getReturnType m)]))))

(defn field [^Class class field]
  (try
    (.getField class (name field))
    (catch NoSuchFieldException _)))

(defn fields [^Class class field]
  (->> class
       .getFields
       (filter #(= (.getName ^Field %) (name field)))
       (map (memfn ^Field getType))))

(defn static-field [sym]
  (let [[_ class field] (re-matches #"(.+?)/(.+)" (str sym))]
    (if (and class field)
      [(symbol class) (symbol field)])))
