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

(fact "The type of a product is (Type n), with n corresponding to a type 1 higher than those used in the abstraction."
      (ecc/check '(product [x Prop] Prop))
      => '(Type 0)
      (ecc/check '(product [x Prop] (Type 0)))
      => '(Type 1)
      (ecc/check '(product [x (Type 0)] Prop))
      => '(Type 1)
      (ecc/check '(product [x (Type 20)] (Type 40)))
      => '(Type 41)
      (ecc/check '(product [x (Type 40)] (Type 10)))
      => '(Type 41))

(fact "A product whose result type is a Prop is itself a Prop"
      (ecc/check '(product [x Prop] x)) => 'Prop)

(fact "The type of a pair is a sum"
      (ecc/check '(pair (sum [x (Type 0)] (Type 0))
                        Prop Prop))
      => '(sum [x (Type 0)] (Type 0)))

(fact "The type of a sum is (Type n), with n corresponding to a type 1 higher than those used in the abstraction."
      (ecc/check '(sum [x Prop] x))
      => '(Type 0)
      (ecc/check '(sum [x Prop] Prop))
      => '(Type 0)
      (ecc/check '(sum [x (Type 41)] Prop))
      => '(Type 42)
      (ecc/check '(sum [x (Type 2)] (Type 41)))
      => '(Type 42))

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

      ;;so NOT the type of the returned object! In other words, no eta-reduction.
      ;;notice that the below reduces to Prop but still checks to (Type 42) instead of (Type 0)
      (ecc/check '((lambda [x (Type 42)] x) Prop))
      => '(Type 42))

(fact "The argument of a function needs to match the declared type"
      (ecc/check '((lambda [x (Type 0)] x) (Type 42)))
      => (throws Error))
