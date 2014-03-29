(ns fun-with-types.logic
  (:refer-clojure :exclude [reduce])
  (:require [fun-with-types.ecc :refer :all]
            [fun-with-types.sugar :refer :all]))

(ecc-macro forall [[var type] prop]
           `(~'product [~var ~type]
                       ~prop))

(ecc-constant implies2
              (function [p1 Prop p2 Prop]
                        (forall [x p1] p2)))

(defn expand-nary [sym fst scnd lst]
  `(~sym ~fst ~(if (seq lst)
                   (expand-nary sym scnd (first lst) (next lst))
                   scnd)))

(defmacro ecc-nary [name expansion]
  `(ecc-macro ~name [fst# scnd# & lst#]
              (expand-nary '~expansion fst# scnd# lst#)))

(ecc-nary implies implies2)

(ecc-constant true
              (forall [x Prop] (implies2 x x)))

(ecc-constant false
              (forall [x Prop] x))

(ecc-constant and2
              (function [p1 Prop p2 Prop]
                        (forall [X Prop]
                                (implies2 (implies2 p1 (implies p2 X))
                                         X))))

(ecc-nary and and2)

(ecc-constant or2
              (function [p1 Prop p2 Prop]
                        (forall [X Prop]
                                (implies (implies p1 X)
                                         (implies p2 X)
                                         X))))
(ecc-nary or or2)

(ecc-constant not
              (function [p Prop]
                        (implies p false)))

(ecc-macro exists [[x type] prop]
           `(~'forall [X# ~'Prop]
                      (~'implies (~'forall [~x ~type]
                                           (~'implies ~prop X#))
                                 X#)))