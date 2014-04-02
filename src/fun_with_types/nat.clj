(ns fun-with-types.nat
  (:refer-clojure :exclude [reduce reduced?])
  (:require [fun-with-types.ecc :refer :all]))

;;This is a quick and dirty implementation for natural numbers.
;;It would be terribly annoying to have to build all datatypes by hand like this.
;;However, it's nice to have something to experiment with.

(ecc-element Nat (Type 0))
(ecc-element 0 Nat)

(expr succ [n]
      :check
      (do (assert (matching-type? 'Nat (check n c) c))
          'Nat)
      :reduce
      `(~'succ ~(reduce n c))
      :substitute
      `(~'succ ~(substitute n sym replacement)))

(expr RecNat [Nat->Type el0 eln->eln+1 n]
      :check
      (do (assert (matching-type? '(product [x Nat] (Type 0)) (check Nat->Type c) c))
          (assert (matching-type? `(~Nat->Type 0) (check el0 c) c))
          (assert (matching-type? `(~'product [x# ~'Nat]
                                              (~'product [c# (~Nat->Type x#)]
                                                         (~Nat->Type (~'succ x#))))
                                  (check eln->eln+1 c)
                                  c))
          (assert (matching-type? 'Nat (check n) c))
          (reduce `(~Nat->Type ~n) c))
      :reduce
      (cond
       (= n 0) (reduce el0 c)
       (succ-expression? n) (reduce `(~eln->eln+1 ~(second n) (~'RecNat ~Nat->Type ~el0 ~eln->eln+1 ~(second n)))
                                    c))
      :substitute
      `(~'RecNat
        ~(substitute Nat->Type sym replacement)
        ~(substitute el0 sym replacement)
        ~(substitute eln->eln+1 sym replacement)
        ~(substitute n sym replacement)))
