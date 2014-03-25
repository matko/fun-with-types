(ns fun-with-types.ecc
  (:refer-clojure :exclude [reduce])
  (:require [clojure.walk :refer [postwalk-replace]]))

(defn error
  "lazy error handling"
  [fmt & args]
  (throw (Exception. (apply format fmt args))))

;;context functions
(defn var-exists? [context var]
  (boolean (first (filter #(= var (first %)) context))))

(defn var-type [context var]
  {:pre [(var-exists? context var)]}
  (second (first (filter #(= var (first %))
                         context))))

;;all check functions return types!

(defn dispatch-check
  ([e c]
     (cond (seq? e)
           (first e)
           (symbol? e)
           :symbol)))

(defmulti check' #'dispatch-check)
(defmulti reduce' #'dispatch-check)

(defn reduce
  ([e] (reduce e []))
  ([e c]
     {:pre [(check' e c)]}
     (reduce' e c)))

(defn check
  ([e] (check e []))
  ([e c] (reduce (check' e c) c)))


(defn- recognize-expression [e type]
  (and (seq? e)
       (= type (first e))))

(defmacro expr [type [& bindings] & {e-check :check e-reduce :reduce}]
  `(do
     ~@(if e-check `((defmethod check' '~type
                       [~'e ~'c]
                       (~@(if (seq bindings)
                            `(let [[_# ~@bindings] ~'e])
                            `(do))
                        ~e-check))))
     ~@(if e-reduce `((defmethod reduce' '~type
                        [~'e ~'c]
                        (~@(if (seq bindings)
                             `(let [[_# ~@bindings] ~'e])
                             `(do))
                         ~e-reduce))))
     ;;argh this macro wants to do way too much
     ;;please somehow split this out we cannot generalize to this extent
     (defn- ~(symbol (str type "-expression?"))
       [~'e]
       (recognize-expression ~'e '~type))))

(expr :symbol []
      :check
      (case e
        Prop '(Type 0)
        (var-type c e))
      :reduce e)

(expr Type []
      :check
      (do 
        (assert (= (first e) 'Type))
        (assert (number? (second e)))
        `(~'Type ~(inc (second e))))
      :reduce e)

;;lambda is of this form:
;;(lambda [:var type] term)
(expr lambda [[var type] term]
      :check
      (do
        (assert (symbol? var))
        (check type c)
        `(~'product [~var ~type] 
                    ~(check term (conj c [var type]))))

      :reduce
      `(~'lambda [~var ~(reduce type c)]
                 ~(reduce term (conj  c [var type]))))



(defn largest-type
  "Returns the largest of the types. Both arguments are to be either Prop or (Type n)."
  [t1 t2]
  {:pre [(letfn [(valid? [t]
                   (or (= 'Prop t)
                       (= 'Type (first t))))]
           (and (valid? t1)
                (valid? t2)))]}

  (cond
   (= t1 'Prop)
    t2
    (= t2 'Prop)
    t1
    (> (second t1) (second t2))
    t1
    :default
    t2))

(expr product [[var type] result-type]
      :check
      (let [type-type (check type c)
            type-result-type (check result-type (conj c [var type]))]
        (if (= 'Prop type-result-type)
          'Prop
          (largest-type type-type type-result-type)))
      :reduce
      `(~'product [~var ~(reduce type c)]
                  ~(reduce result-type (conj c [var type]))))

;;TODO this should rename variables before checking equality so that
;; (lambda [x Prop] x)
;;is the same as
;; (lambda [y Prop] y)
(defn- equal-term? [t1 t2 c]
  (= (reduce t1 c)
     (reduce t2 c)))

(defn- matching-type?
  "type matches comparison-type if they're equal (reduced) terms, or if comparison-type is a (Type n1) and type is a Prop or a (Type n2) with n2<n1.
This relation is not transitive!"
  [type comparison-type c]
  (let [rtype (reduce type c)
        rcomparison-type (reduce type c)]
    (or (equal-term? rtype rcomparison-type c)
        (and (Type-expression? rcomparison-type)
             (or (= 'Prop rtype)
                 (and (Type-expression? rtype)
                      (< (second rtype)
                         (second rcomparison-type))))))))

(defn- substitute
  "Substitute a variable for a term in another term. This does not perform any checks."
  [var term original]
  (postwalk-replace {var term}
                    original))

(expr :default []
      :check
      (let [[function argument] e
            function-type (check function c)
            argument-type (check argument c)]
        (assert (product-expression? function-type))
        (let [[_ [var function-argument-type]
               function-result-type] function-type]
          (assert (matching-type? argument-type
                                  function-argument-type
                                  c))
          (substitute var argument function-result-type)))

      :reduce
      (let [[function argument] e
            [_ [var _] result-expression] (reduce function c)
            argument (reduce argument c)]
        (substitute var argument result-expression)))

(expr sum [[var type] second-type]
      :check
      (let [type-type (check type c)
            type-second-type (check second-type (conj c [var type]))]
        (largest-type type-type type-second-type))

      :reduce
      `(sum [var ~(reduce type c)]
            ~(reduce second-type (conj c [var ~(reduce type c)]))))

