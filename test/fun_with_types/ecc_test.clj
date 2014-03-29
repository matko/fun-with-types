(ns fun-with-types.ecc-test
  (:use [midje.sweet])
  (:require [fun-with-types.ecc :as ecc]))

(fact "Prop's type is (Type 0), which is of type (Type 1), etc"
      (ecc/check 'Prop) => '(Type 0)
      (letfn [(texp [n] (list 'Type n))]
        (map (comp ecc/check texp) (range 10))
        => (map texp (range 1 11))))
