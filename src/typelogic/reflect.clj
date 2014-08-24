(ns typelogic.reflect
  (:refer-clojure :exclude [supers methods isa?])
  (:require [clojure.core :as core])
  (:import [java.lang.reflect Modifier Method Field Constructor]))

(defn final? [^Class class]
  (and (class? class)
       (or (Modifier/isFinal (.getModifiers class))
           (.isPrimitive class))))

(defn constructors [^Class class]
  (->> class (.getConstructors) (map #(vec (.getParameterTypes ^Constructor %)))))

(defn methods [^Class class method]
  (->> class
       (.getMethods)
       (filter #(= (.getName ^Method %) (name method)))
       (map (fn [^Method m] [(vec (.getParameterTypes m)) (.getReturnType m)]))))

(defn field [^Class class field]
  (.getField class (name field)))

(defn static-field [sym]
  (let [[_ class field] (re-matches #"(.+?)/(.+)" (str sym))]
    (if (and class field)
      [(symbol class) (symbol field)])))

(defn tag [sym]
  (if-let [var (some-> sym meta :tag resolve)]
    (if (class? var) var)))
