(ns fun-with-types.engine
  (:refer-clojure :exclude [reduce reduced?])
  (:require [clojure.edn :as edn]
            [clojure.java.io :refer [reader resource file]]
            [fun-with-types.ecc :refer :all]
            [fun-with-types.sugar :refer :all]
            fun-with-types.logic
            fun-with-types.nat)
  (:import java.io.PushbackReader))

(defn eval-dispatch-fn [expr context]
  (if (sym? expr)
    :symbol
    (first expr)))

(defmulti fwt-eval' #'eval-dispatch-fn)

(defn symbolize [e]
  (clojure.walk/postwalk (fn [e]
                           (if (= (type e)
                                  Boolean)
                             (symbol (str e))
                             e))
                         e))

(defn fwt-eval
  ([e] (fwt-eval e []))
  ([e c] (fwt-eval' (symbolize e) c)))

(defn add-context [expression context]
  (if (empty? context)
    expression
    `(~'let [~@(apply concat context)]
       ~expression)))

(defmethod fwt-eval' :default
  [expression c]
  (check (add-context expression c))
  c)



(defmethod fwt-eval' 'def
  [[_ name definition] c]
  (check (add-context definition c))
  (conj c [name definition]))


(defmethod fwt-eval' 'check
  [[_ expression] c]
  (println (check (add-context expression c)))
  c)

(defmethod fwt-eval' 'reduce
  [[_ expression] c]
  (println (reduce (add-context expression c)))
  c)

(defmethod fwt-eval' 'assert-type
  [[_ type term] c]
  (assert (matching-type? (add-context type c)
                          (check (add-context  term c))
                          ()))
  c)

(defn fwt-do-fn [& expressions]
  (clojure.core/reduce #(try (fwt-eval %2 %1)
                             (catch Throwable e
                               (println "error for expression " %2 "in context" %1)
                               (throw e))) [] expressions))

(defmacro fwt-do [& expressions]
  `(fwt-do-fn ~@(map (fn [e]
                       `(quote ~e))
                     expressions)))

(defn- read-file [path]
  (let [resource
        (if (and  (string? path)
                  (= \: (first path)))
          (resource (apply str "built-in/"
                           (rest path)))
          (if (.exists (file path))
               path))]
    (when-not resource
      (throw (Exception. (str "bad path: " path))))
    (with-open [in (PushbackReader. (reader resource))]
      (loop [e (edn/read {:eof nil} in)
             coll []]
        (if e (recur (edn/read {:eof nil} in)
                     (conj coll e))
            coll)))))

(defn fwt-load [path]
  (apply fwt-do-fn (read-file path)))
