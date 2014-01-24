(ns typelogic.reflect
  (:refer-clojure :exclude [supers methods isa?])
  (:require [clojure.core :as core])
  (:import [java.lang.reflect Method Field Constructor]))

(def primitives
  {'long Long/TYPE
   'double Double/TYPE})

(defn tag->class [tag]
  (get primitives tag (resolve tag)))

(defn methods [^Class class method]
  (->> class
       .getMethods
       (filter #(= (.getName ^Method %) (name method)))
       (map #(cons (.getReturnType ^Method %) (.getParameterTypes ^Method %)))))

(defn fields [^Class class field]
  (->> class
       .getFields
       (filter #(= (.getName ^Field %) (name field)))
       (map (memfn ^Field getType))))

(defn constructors [^Class class]
  (->> class
       .getConstructors
       (map #(cons class (.getParameterTypes ^Constructor %)))))

(defn field [sym]
  (let [[_ class field] (re-matches #"(.*)/(.*)" (str sym))]
    (prn class field)
    (if (and class field)
      (list '. (symbol class) (symbol field)))))
