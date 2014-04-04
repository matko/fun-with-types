(ns fun-with-types.ecc
  (:refer-clojure :exclude [reduce reduced?])
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
           :default
           :symbol)))

(defmulti check' #'dispatch-check)
(defmulti reduce' #'dispatch-check)
(defmulti substitute #'dispatch-check)

(defn reduced? [expression]
  (:reduced? (meta expression)))

(defn sym? [x] (or (symbol? x)
                   (keyword? x)
                   (and (integer? x)
                        (>= x 0))))

(defn reduce
  ([e] (reduce e ()))
  ([e c]
     {:pre [(or (reduced? e) ;if this was previously reduced, it has already passed checks
                (check' e c))
            (seq? c)]}
     (if (reduced? e)
       e
       (let [reduced (reduce' e c)]
         (if (or (symbol? reduced)
                 (seq? reduced))
           (with-meta reduced
             {:reduced? true})
           reduced)))))

(defn check
  ([e] (check e ()))
  ([e c]
     {:pre [(seq? c)]}
     (reduce (check' e c) c)))


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

(defonce *constant-table* (atom {}))

(defn ecc-add-constant [var val]
  (let [result (check val)]
    (swap! *constant-table* assoc var val)
    result))

(defn ecc-remove-constant [var]
  (swap! *constant-table* dissoc var))

(defmacro ecc-constant [var val]
  `(ecc-add-constant '~var '~val))

(expr Type []
      :check
      (do
        (assert (= (first e) 'Type))
        (assert (number? (second e)))
        `(~'Type ~(inc (second e))))
      :reduce e
      :substitute e)


(defn type? [e c]
  (let [e (check e c)]
    (or (= e 'Prop)
        (Type-expression? e))))

(defonce *element-table* (atom {}))

(defn ecc-add-element [element type]
  (assert (type? type ()))
  (swap! *element-table* assoc element type))

(defn ecc-remove-element [element]
  (swap! *element-table* dissoc element))

(defmacro ecc-element [element type]
  `(ecc-add-element '~element '~type))

(expr :symbol []
      :check
      (if-let [constant (@*constant-table* e)]
        (check constant c)
        (if-let [element-type (@*element-table* e)]
          element-type
          (case e
            Prop '(Type 0)
            (var-type c e))))
      :reduce
      (if-let [constant (@*constant-table* e)]
        (reduce' constant c)
        e)
      :substitute
      (if (= sym e)
        replacement
        e)
      )


(defn rebind-var [term c]
  (let [[functional [var type] result-term] term
        new-var (if (var-exists? c var)
                  (gensym (str var "-"))
                  var)
        result-term (substitute result-term var new-var)]
    `(~functional [~new-var ~type] ~result-term)))




;;lambda is of this form:
;;(lambda [:var type] term)
(expr lambda [[var type] term]
      :check
      (do
        (assert (sym? var))
        (assert (type? type c))
        (check type c)
        `(~'product [~var ~type] 
                    ~(check term (conj c [var type]))))

      :reduce
      `(~'lambda [~var ~(reduce' type c)]
                 ~(reduce' term (conj  c [var type])))
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
      (do
        (assert (type? type c))
        (assert (type? result-type (conj c [var type])))
        (let [type-type (check type c)
              type-result-type (check result-type (conj c [var type]))]
          (if (= 'Prop type-result-type)
            'Prop
            (largest-type type-type type-result-type))))
      :reduce
      `(~'product [~var ~(reduce' type c)]
                  ~(reduce' result-type (conj c [var type])))
      :substitute
      `(~'product [~var ~(substitute type sym replacement)]
                  ~(if (= sym var) ;shadowing bind, end substitution here
                     result-type
                     (substitute result-type sym replacement))))

(defn binding-form? [e]
  (and (seq? e)
       (some (partial = (first e))
             '[sum product lambda])))

(defn bound-vars [expression context]
  (let [expression (reduce expression context)
        result (atom [])]
    (clojure.walk/prewalk
     (fn [e]
       (when (binding-form? e)
         (swap! result conj (first (second e))))
       e)
     expression)
    @result))

(defn normalize
  ([e s] (normalize e s ()))
  ([e s c]
     (let [e (reduce e c)
           i (atom 0)]
       (clojure.walk/prewalk
        (fn [e]
          (if (binding-form? e)
            (let [[binding [var type] result] e
                  new-var (symbol (str s "-" (swap! i inc)))]
              `(~binding [~new-var ~type]
                 ~(substitute result var new-var)))
            e))
        e))))

(defn equal-term? [t1 t2 c]
  (let [s (gensym "var-")]
    (= (normalize t1 s c)
       (normalize t2 s c))))

(declare matching-type? sum-expression? product-expression?)

(defn- matching-type-pair?
  [[_ [va t1-a] t2-a]
   [_ [vb t1-b] t2-b]
   c]
  ;;NOTE: I'm making matching-type? do the reduction for both types.
  ;;this happens in the same context for both, which technically is not right for the var-type.
  ;;nevertheless, var should not appear free in var-type, so this should work.
  (and (matching-type? t1-a t2-a (conj c [va t1-a]))
       (matching-type? t1-b t2-b (conj c [vb t1-b]))))

(defn matching-type?
  "type matches comparison-type if they're equal (reduced) terms, or if comparison-type is a (Type n1) and type is a Prop or a (Type n2) with n2<n1, or if type and comparison-type are dependent products or strong sum, whose components match type.
This relation is not transitive!"
  [type comparison-type c]
  (let [rtype (reduce type c)
        rcomparison-type (reduce comparison-type c)]
    (or (equal-term? rtype rcomparison-type c)
        (and (or (and (product-expression? rtype)
                      (product-expression? rcomparison-type))
                 (and (sum-expression? rtype)
                      (sum-expression? rcomparison-type)))
             (matching-type-pair? rtype rcomparison-type c))
        (and (Type-expression? rtype)
             (or (= 'Prop rcomparison-type)
                 (and (Type-expression? rcomparison-type)
                      (< (second rcomparison-type)
                         (second rtype))))))))

;;function calls
(expr :default []
      :check
      (let [[function & arguments] e
            function-type (check function c)]
        (assert (product-expression? function-type))
        (loop [[_ [var function-argument-type] function-result-type] function-type
               [argument & arguments] arguments]
          (let [argument-type (check argument c)]
            (assert (matching-type? function-argument-type
                                    argument-type
                                    c))
            (let [result (substitute function-result-type var argument)]
              (if (seq arguments)
                (recur result arguments)
                result)))
          ))

      :reduce
      (let [[function & arguments] e]
        (if (sym? function)
          e
          (loop [[_ [var _] result-expression] (reduce' function c)
                 [argument & arguments] arguments]
            (let [result (reduce' (substitute result-expression var argument) c)]
              (if (seq arguments)
                (recur result arguments)
                result))
            )))
      :substitute
      (let [[function & arguments] e]
        `(~(substitute function sym replacement)
          ~@(map #(substitute % sym replacement)
                 arguments))))

(expr sum [[var type] second-type]
      :check
      (let [type-type (check type c)
            type-second-type (check second-type (conj c [var type]))]
        (largest-type type-type type-second-type))

      :reduce
      `(~'sum [~var ~(reduce' type c)]
              ~(reduce' second-type (conj c [var (reduce' type c)])))
      :substitute
      `(~'sum [~var ~(substitute type sym replacement)]
            ~(if (= sym var) ;binding
               second-type
               (substitute second-type sym replacement))))

(expr pair [sum-type left right]
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
      `(~'pair ~(reduce' sum-type c)
               ~(reduce' left c)
               ~(reduce' right c))
      :substitute
      `(~'pair ~(substitute sum-type sym replacement)
               ~(substitute left sym replacement)
               ~(substitute right sym replacement)))

(expr left [pair]
      :check
      (let [pair (reduce pair c)]
        (assert (pair-expression? pair))
        (let [[_ sum-type left right] pair
              sum-type (reduce sum-type)]
          (assert (sum-expression? sum-type))
          (let [[_ [_ type] _] sum-type]
            type)))
      :reduce
      (let [pair (reduce' pair c)]
        (assert (pair-expression? pair))
        (let [[_ sum-type left right] pair]
          (reduce' left)))
      :substitute
      `(~'left ~(substitute pair sym replacement)))

(expr right [pair]
      :check
      (let [pair (reduce pair c)]
        (assert (pair-expression? pair))
        (let [[_ sum-type left right] pair
              sum-type (reduce sum-type)]
          (assert (sum-expression? sum-type))
          (let [[_ [var left-type] right-type] sum-type]
            (substitute right-type var left))))
      :reduce
      (let [pair (reduce' pair c)]
        (assert (pair-expression? pair))
        (let [[_ sum-type left right] pair]
          (reduce' right)))
      :substitute
      `(~'left ~(substitute pair sym replacement)))

;;This is a VERY UGLY HACK but it works.
;;check without context throws an exception if it encounters a symbol other than a constant.
(defn fully-expanded? [e]
  (try
    (do (check e)
        true)
    (catch Exception _ false)))
