(ns fun-with-types.ecc-test
  (:use [midje.sweet])
  (:require [fun-with-types.ecc :as ecc]))

(defn texp [n]
  (list 'Type n))

(fact "Prop's type is (Type 0), which is of type (Type 1), etc"
      (ecc/check 'Prop) => '(Type 0)
      (map (comp ecc/check texp) (range 10))
      => (map texp (range 1 11)))

(fact "Prop and (Type n) expressions reduce to themselves"
      (ecc/reduce 'Prop) => 'Prop
      (let [types (map texp (range 10))]
        (map ecc/reduce types) => types))

(fact "The type of a lambda is a product"
      (ecc/check '(lambda [x Prop]
                          Prop))
      => '(product [x Prop] (Type 0)))

(fact "A product whose result type is a Prop is itself a Prop"
      (ecc/check '(product [x Prop] x)) => 'Prop)

(fact "The type of a pair is a sum"
      (ecc/check '(pair (sum [x (Type 0)] (Type 0))
                        Prop Prop))
      => '(sum [x (Type 0)] (Type 0)))

(fact "The objects in a pair need to match the declared sum type."
      (ecc/check '(pair (sum [x (Type 0)] (Type 0))
                        Prop
                        Prop))
      => TRUTHY
      (ecc/check '(pair (sum [x (Type 0)] (Type 0))
                        Prop
                        (Type 1)))
      => (throws Error)
      (ecc/check '(pair (sum [x (Type 0)] (Type 0))
                        (Type 1)
                        Prop))
      => (throws Error)
)

(fact "The type of a function call is the type of the function result after substitution"
      (ecc/check '((lambda [x (Type 0)] (Type 41)) Prop))
      => '(Type 42)

      ;;so NOT the type of the returned object!
      ;;notice that the below reduces to Prop but still checks to (Type 42) instead of (Type 1)
      (ecc/check '((lambda [x (Type 42)] x) Prop))
      => '(Type 42))
