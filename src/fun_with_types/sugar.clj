(ns fun-with-types.sugar
  (:refer-clojure :exclude [reduce reduced?])
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

(defn add-defs-to-context [defs context]
  (seq (concat (partition 2 defs) context)))

(defn ecc-let-build-function-list [definitions context]
  (clojure.core/reduce (fn [prev [var def]]
                         `[~@prev ~var ~(check def
                                               (add-defs-to-context prev context))])
                       []
                       definitions))

(defn ecc-let-build-arg-list [definitions function-list arg-list context]
  (if (seq? definitions)
    (let [[[var def] & definitions] definitions]
      (recur definitions
             `[~@function-list ~var ~(check def
                                           (add-defs-to-context function-list context))]
             `[~@arg-list ~(if (seq function-list)
                             (reduce `((~'function [~@function-list]
                                                   ~def)
                                       ~@arg-list)
                                     context)
                             def)]
             context)
      )
    arg-list))


(ecc-macro let [[& definitions] expression]
           (let [definitions (partition 2 definitions)
                 function-list (ecc-let-build-function-list definitions c)
                 function-args (ecc-let-build-arg-list definitions [] [] c)]
             `((~'function [~@function-list]
                           ~expression)
               ~@function-args)))






