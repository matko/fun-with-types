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
  {:pre [(or (var-exists? context var)
             (error "no such var: %s" var))]}
  (second (first (filter #(= var (first %))
                         context))))

;;all check functions return types!

(defn dispatch-check
  ([e & _]
     (cond (seq? e)
           (first e)
           (symbol? e)
           :symbol)))

(defmulti check' #'dispatch-check)
(defmulti reduce' #'dispatch-check)
(defmulti substitute #'dispatch-check)

(defn reduce
  ([e] (reduce e []))
  ([e c]
     {:pre [(check' e c)]}
     (reduce' e c)))

(defn check
  ([e] (check e []))
  ([e c] (reduce (check' e c) c)))


(defn recognize-expression [e type]
  (and (seq? e)
       (= type (first e))))

(defmacro expr [type [& bindings] & {e-check :check e-reduce :reduce e-substitute :substitute}]
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
     ~@(if e-substitute `((defmethod substitute '~type
                            [~'e ~'sym ~'replacement]
                            (~@(if (seq bindings)
                                 `(let [[_# ~@bindings] ~'e])
                                 `(do))
                             ~e-substitute))))
     ;;argh this macro wants to do way too much
     ;;please somehow split this out we cannot generalize to this extent


     (defn ~(symbol (str type "-expression?"))
       [~'e]
       (recognize-expression ~'e '~type))))

(expr :symbol []
      :check
      (case e
        Prop '(Type 0)
        (var-type c e))
      :reduce e
      :substitute
      (if (= sym e)
        replacement
        e)
      )

(expr Type []
      :check
      (do 
        (assert (= (first e) 'Type))
        (assert (number? (second e)))
        `(~'Type ~(inc (second e))))
      :reduce e
      :substitute e)

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
                 ~(reduce term (conj  c [var type])))
      :substitute
      `(~'lambda [~var ~(substitute type sym replacement)]
                 ~(if (= sym var) ;this binding shadows, so replacement ends her
                    term
                    (substitute term sym replacement))))



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
                  ~(reduce result-type (conj c [var type])))
      :substitute
      `(~'product [~var ~(substitute type sym replacement)]
                  ~(if (= sym var) ;shadowing bind, end substitution here
                     result-type
                     (substitute result-type sym replacement)))

      ;;TODO this should rename variables before checking equality so that
      ;; (lambda [x Prop] x)
      ;;is the same as
      ;; (lambda [y Prop] y)
)
(defn equal-term? [t1 t2 c]
  (= (reduce t1 c)
     (reduce t2 c)))

;;TODO there are other matching types. strong sums and dependent products also have a hierarchy
(defn matching-type?
  "type matches comparison-type if they're equal (reduced) terms, or if comparison-type is a (Type n1) and type is a Prop or a (Type n2) with n2<n1.
This relation is not transitive!"
  [type comparison-type c]
  (let [rtype (reduce type c)
        rcomparison-type (reduce comparison-type c)]
    (or (equal-term? rtype rcomparison-type c)
        (and (Type-expression? rtype)
             (or (= 'Prop rcomparison-type)
                 (and (Type-expression? rcomparison-type)
                      (< (second rcomparison-type)
                         (second rtype))))))))

;;function calls
(expr :default []
      :check
      (let [[function argument] e
            function-type (check function c)
            argument-type (check argument c)]
        (assert (product-expression? function-type))
        (let [[_ [var function-argument-type]
               function-result-type] function-type]
          (assert (matching-type? function-argument-type
                                  argument-type
                                  c))
          (substitute function-result-type var argument)))

      :reduce
      (let [[function argument] e
            [_ [var _] result-expression] (reduce function c)
            argument (reduce argument c)]
        (substitute result-expression var argument))
      :substitute
      (let [[function argument] e]
        `(~(substitute function sym replacement)
          ~(substitute argument sym replacement))))

(expr sum [[var type] second-type]
      :check
      (let [type-type (check type c)
            type-second-type (check second-type (conj c [var type]))]
        (largest-type type-type type-second-type))

      :reduce
      `(~'sum [~var ~(reduce type c)]
            ~(reduce second-type (conj c [var (reduce type c)])))
      :substitute
      `(~'sum [~var ~(substitute type sym replacement)]
            ~(if (= sym var) ;binding
               second-type
               (substitute second-type sym replacement))))

(expr pair [left right sum-type]
      :check
      (let [sum-type (reduce sum-type c)]
        (assert (sum-expression? sum-type))
        (let [[_ [var left-type] right-type] sum-type]
          (assert (matching-type? left-type
                                  (check left c)
                                  c))
          (assert (matching-type? (substitute right-type var left)
                                  (check right c)
                                  c))
          sum-type))
      :reduce
      `(~'pair ~(reduce left c)
               ~(reduce right c)
               ~(reduce sum-type c))
      :substitute
      (do (println 'lols)
          `(~'pair ~(substitute left sym replacement)
                   ~(substitute right sym replacement)
                   ~(substitute sum-type sym replacement))))

(expr left [pair]
      :check
      (let [pair (reduce pair c)]
        (assert (pair-expression? pair))
        (let [[_ left right sum-type] pair
              sum-type (reduce sum-type)]
          (assert (sum-expression? sum-type))
          (let [[_ [_ type] _] sum-type]
            type)))
      :reduce
      (let [pair (reduce pair c)]
        (assert (pair-expression? pair))
        (let [[_ left right sum-type] pair]
          (reduce left)))
      :substitute
      `(~'left ~(substitute pair sym replacement)))

(expr right [pair]
      :check
      (let [pair (reduce pair c)]
        (assert (pair-expression? pair))
        (let [[_ left right sum-type] pair
              sum-type (reduce sum-type)]
          (assert (sum-expression? sum-type))
          (let [[_ [var left-type] right-type] sum-type]
            (substitute right-type var left))))
      :reduce
      (let [pair (reduce pair c)]
        (assert (pair-expression? pair))
        (let [[_ left right sum-type] pair]
          (reduce right)))
      :substitute
      `(~'left ~(substitute pair sym replacement)))
