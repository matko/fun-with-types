(ns fun-with-types.engine
  (:refer-clojure :exclude [reduce])
  (:require [fun-with-types.ecc :refer :all]
            [fun-with-types.sugar :refer :all]))

(defn eval-dispatch-fn [expr context]
  (if (symbol? expr)
    :symbol
    (first expr)))

(defmulti fwt-eval' #'eval-dispatch-fn)

(defn fwt-eval
  ([e] (fwt-eval e []))
  ([e c] (fwt-eval' e c)))

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
  (clojure.core/reduce #(fwt-eval' %2 %1) [] expressions))

(defmacro fwt-do [& expressions]
  `(fwt-do-fn ~@(map (fn [e]
                       `(quote ~e))
                     expressions)))
