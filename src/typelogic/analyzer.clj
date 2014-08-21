(ns typelogic.analyzer
  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic :refer :all])
  (:import [java.lang.reflect Modifier Method Field Constructor]))

(def analyze)

(defmulti analyze-app
  (fn [ctx & exprs]
    (first exprs)))

(defmethod analyze-app 'def [ctx tag name & expr]
  (let [var (lvar name)]
    (list* tag var (map #(analyze (assoc ctx name var) %) expr))))

(defmethod analyze-app 'if [ctx tag & exprs]
  (cons tag (map #(analyze ctx %) exprs)))

(defmethod analyze-app 'do [ctx tag & exprs]
  (cons tag (map #(analyze ctx %) exprs)))

(defn analyze-tag [sym]
  (if-let [var (some-> sym meta :tag resolve)]
    (if (class? var) var)))

(defn analyze-bindings [ctx bindings exprs]
  (let [[ctx bindings] (reduce (fn [[ctx bindings] [sym expr]]
                                 (let [type (or (analyze-tag sym) (lvar sym))
                                       ctx (assoc ctx sym type)]
                                   [ctx (conj bindings [type (analyze ctx expr)])]))
                               [ctx []]
                               (partition 2 bindings))]
    (cons bindings (map #(analyze ctx %) exprs))))

(defmethod analyze-app 'let* [ctx tag bindings & exprs]
  (cons tag (analyze-bindings ctx bindings exprs)))

(defmethod analyze-app 'quote [ctx tag & exprs]
  (class (first exprs)))

(defmethod analyze-app 'var [ctx tag & exprs])

(defn analyze-fn [ctx params & exprs]
  (let [[ctx params] (reduce (fn [[ctx params] sym]
                               (let [type (or (analyze-tag sym) (lvar sym))]
                                 [(assoc ctx sym type) (conj params type)]))
                             [ctx []]
                             params)]
    (list* params (map #(analyze ctx %) exprs))))

(defmethod analyze-app 'fn* [ctx tag expr & exprs]
  (loop [ctx ctx, var (lvar), expr expr, exprs exprs]
    (cond (symbol? expr) (let [var (lvar expr)
                               [expr' & exprs'] exprs]
                           (recur (assoc ctx expr var) var expr' exprs'))
          (vector? expr) (recur ctx var (cons expr exprs) nil)
          (seq? expr) (list* tag var (map #(apply analyze-fn ctx %) (cons expr exprs))))))

(defmethod analyze-app 'loop* [ctx tag bindings & exprs]
  (cons tag (analyze-bindings ctx bindings exprs)))

(defmethod analyze-app 'recur [ctx tag & exprs]
  (cons tag (map #(analyze ctx %) exprs)))

(defn analyze-object [ctx expr]
  (or (and (symbol? expr) (resolve expr))
      (analyze ctx expr)))

(defn analyze-method [ctx ^Class class method & args]
  (if-let [methods (->> (.getMethods class)
                        (filter #(= (.getName ^Method %) (name method)))
                        (seq))]
    (cons (->> methods
               (map #(list (vec (.getParameterTypes ^Method %))
                           (.getReturnType ^Method %)))
               (list* 'fn* (lvar method)))
          (map #(analyze ctx %) args))))

(defn analyze-field [^Class class field]
  (.getType (.getField class (name field))))

(defmethod analyze-app '. [ctx tag expr member & args]
  (let [^Class class (analyze-object ctx expr)]
    (if (class? class)
      (cond (seq? member) (apply analyze-method ctx class member)
            (symbol? member) (or (apply analyze-method ctx class member args)
                                 (analyze-field class member)))
      (throw (ex-info "No matching member found") {:member member :class class}))))

(defmethod analyze-app 'new [ctx tag name & args]
  (let [^Class class (and (symbol? name) (resolve name))]
    (if (class? class)
      (cons (->> (.getConstructors class)
                 (map #(list (vec (.getParameterTypes ^Constructor %)) class))
                 (list* 'fn* (lvar name)))
            (map #(analyze ctx %) args))
      (throw (ex-info "Unable to resolve classname" {:class name})))))

(defmethod analyze-app :default [ctx & exprs]
  (map #(analyze ctx %) exprs))

(defn analyze [ctx expr]
  (cond (seq? expr) (apply analyze-app ctx (macroexpand expr))
        (symbol? expr) (or (ctx expr)
                           (analyze ctx (resolve expr))
                           (throw (ex-info "Unable to resolve symbol" {:symbol expr})))
        (var? expr) expr
        :else (class expr)))
