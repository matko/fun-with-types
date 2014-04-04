(ns fun-with-types.logic
  (:refer-clojure :exclude [reduce reduced?])
  (:require [fun-with-types.ecc :refer :all]
            [fun-with-types.sugar :refer :all]))

(ecc-macro forall [[var type] prop]
           `(~'product [~var ~type]
                       ~prop))

(defn expand-nary [sym fst scnd lst]
  `(~sym ~fst ~(if (seq lst)
                 (expand-nary sym scnd (first lst) (next lst))
                 scnd)))

(ecc-macro exists [[x type] prop]
           `(~'forall [X# ~'Prop]
                      (~'implies (~'forall [~x ~type]
                                           (~'implies ~prop X#))
                                 X#)))

(defmacro ecc-nary [name expansion]
  `(ecc-macro ~name [fst# scnd# & lst#]
              (expand-nary '~expansion fst# scnd# lst#)))

(ecc-nary implies implies2)
(ecc-nary and and2)
(ecc-nary or or2)
