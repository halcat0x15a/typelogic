(ns typelogic.reflect
  (:refer-clojure :exclude [methods])
  (:import [java.lang.reflect Method Field Constructor]))

(defn method [^Class class method & parameter-types]
  (doto (.getDeclaredMethod class (name method) (into-array Class parameter-types))
    (.setAccessible true)))

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

(defn function [return-type parameter-types]
  (apply vector :typelogic.core/fn return-type parameter-types))

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

(def numbers
  [Long/TYPE Integer/TYPE Double/TYPE Float/TYPE
   Long Integer Double Float])

(defn infer [x]
  (try
    (let [expr (Compiler/analyze clojure.lang.Compiler$C/STATEMENT x)
          type (class expr)]
      (cond (number? x) (concat numbers (supers (class x)))
            (-> type (method 'hasJavaClass) (invoke expr) boolean)
            (let [class (-> type (method 'getJavaClass) (invoke expr))]
              (cons class (supers class)))
            :else [nil]))
    (catch Exception _ [nil])))
