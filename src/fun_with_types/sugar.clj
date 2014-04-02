(ns fun-with-types.sugar
  (:refer-clojure :exclude [reduce])
  (:require [fun-with-types.ecc :refer [expr check reduce substitute sum-expression?]]))


(defmacro ecc-macro [name [& args] expansion]
  `(expr ~name [~@args]
         :check (check ~expansion ~'c)
         :reduce (reduce ~expansion ~'c)
         :subsitute (substitute ~expansion ~'sym ~'replacement)))

(defn functional-sugar-fn [expand-sym vars-and-types result]
  (loop [result result
         [[var type] & vars-and-types] 
         (reverse (partition 2 vars-and-types))]
    (if var
      (recur `(~expand-sym [~var ~type]
                        ~result)
             vars-and-types)
      result)))

(defmacro functional-sugar [name expand-sym]
  `(ecc-macro ~name [[& vars-and-types#] result#]
              (functional-sugar-fn '~expand-sym vars-and-types# result#)))

;;these are syntactically very similar, no sense in duplicating code.
(functional-sugar function lambda)
(functional-sugar ftype product)

(ecc-macro struct [& vars-and-types]
           (loop [result (last vars-and-types)
                  [[var type] & vars-and-types]
                  (reverse (partition 2 vars-and-types))]
             (if var
               (recur `(~'sum [~var ~type]
                              ~result)
                      vars-and-types)
               result)))

(ecc-macro tuple [struct-type & elements]
           (let [sum-type (reduce struct-type)]
             (assert (odd? (count elements)))
             (letfn [(build-pairs [[_ [_ _] right-type :as sum-type] [element & elements]]
                       (if (seq elements)
                         `(~'pair ~sum-type
                                  ~element
                                  ~(if (> (count elements) 1)
                                     (build-pairs (if (sum-expression? right-type)
                                                    right-type)
                                                  elements)
                                    (first elements)))))]
               (build-pairs sum-type elements))))

(ecc-macro let [[& definitions] expression]
           (let [definitions (partition 2 definitions)
                 function-list (clojure.core/reduce (fn [prev [var def]]
                                                      `[~@prev ~var ~(check def c)])
                                                    []
                                                    definitions)
                 defs (map second definitions)]
             `((~'function [~@function-list]
                           ~expression)
               ~@defs)))
