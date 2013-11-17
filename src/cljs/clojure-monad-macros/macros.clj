(ns clojure-monad-macros.macros
  (:require [clojure.string])
  )

;; copied from  https://github.com/clojure/tools.macro/blob/master/src/main/clojure/clojure/tools/macro.clj
;; 
;; 
; A set of all special forms. Special forms are not macro-expanded, making
; it impossible to shadow them by macro definitions. For most special
; forms, all the arguments are simply macro-expanded, but some forms
; get special treatment.
(def ^{:private true} special-forms
  (into #{} (keys clojure.lang.Compiler/specials)))
; Value in Clojure 1.2 and 1.3:
; #{deftype* new quote & var set! monitor-enter recur . case* clojure.core/import* reify* do fn* throw monitor-exit letfn* finally let* loop* try catch if def}

; The following three vars are constantly redefined using the binding
; form, imitating dynamic scoping.
;
; Local macros.
(def ^{:dynamic true :private true} macro-fns {})
; Local symbol macros.
(def ^{:dynamic true :private true} macro-symbols {})
; Symbols defined inside let forms or function arguments.
(def ^{:dynamic true :private true} protected-symbols #{})

(defn- protected?
  [symbol]
  "Return true if symbol is a reserved symbol (starting or ending with a dot)
   or a symbol bound in a surrounding let form or as a function argument."
  (or (contains? protected-symbols symbol)
      (let [s (str symbol)]
        (or (= "." (subs s 0 1))
            (= "." (subs s (dec (count s))))))))

(defn- expand-symbol
  "Expand symbol macros"
  [symbol]
  (cond (protected? symbol)                   symbol
        (contains? macro-symbols symbol)     (get macro-symbols symbol)
        :else (let [v (try (resolve symbol)
                           (catch java.lang.ClassNotFoundException e nil))
                    m (meta v)]
                (if (:symbol-macro m)
                  (var-get v)
                  symbol))))

(defn- expand-1
  "Perform a single non-recursive macro expansion of form."
  [form]
  (cond
    (seq? form)
      (let [f (first form)]
        (cond (contains? special-forms f)   form
              (and (not (protected? f))
                   (contains? macro-fns f)) (apply (get macro-fns f) (rest form))
              (symbol? f)  (cond
                            (protected? f)  form
                            ; macroexpand-1 fails if f names a class
                            (class? (ns-resolve *ns* f)) form
                            :else    (let [exp (expand-symbol f)]
                                       (if (= exp f)
                                         (clojure.core/macroexpand-1 form)
                                         (cons exp (rest form)))))
              ; handle defmacro macros and Java method special forms
              :else (clojure.core/macroexpand-1 form)))
    (symbol? form)
      (expand-symbol form)
     :else
       form))

(defn- expand
  "Perform repeated non-recursive macro expansion of form, until it no
   longer changes."
  [form]
  (let [ex (expand-1 form)]
    (if (identical? ex form)
      form
      (recur ex))))

(declare expand-all)

(defn- expand-args
  "Recursively expand the arguments of form, leaving its first
   n elements unchanged."
  ([form]
   (expand-args form 1))
  ([form n]
   (doall (concat (take n form) (map expand-all (drop n form))))))

(defn- expand-bindings
  [bindings exprs]
  (if (empty? bindings)
    (list (doall (map expand-all exprs)))
    (let [[[s b] & bindings] bindings]
      (let [b (expand-all b)]
        (binding [protected-symbols (conj protected-symbols s)]
          (doall (cons [s b] (expand-bindings bindings exprs))))))))

(defn- expand-with-bindings
  "Handle let*, letfn* and loop* forms. The symbols defined in them are
   protected from symbol macro expansion, the definitions and the body
   expressions are expanded recursively."
  [form]
  (let [f        (first form)
        bindings (partition 2 (second form))
        exprs    (rest (rest form))
        expanded (expand-bindings bindings exprs)
        bindings (vec (apply concat (butlast expanded)))
        exprs    (last expanded)]
    (cons f (cons bindings exprs))))

(defn- expand-fn-body
  [[args & exprs]]
  (binding [protected-symbols (reduce conj protected-symbols
                                     (filter #(not (= % '&)) args))]
    (cons args (doall (map expand-all exprs)))))

(defn- expand-fn
  "Handle fn* forms. The arguments are protected from symbol macro
   expansion, the bodies are expanded recursively."
  [form]
  (let [[f & bodies] form
        name         (when (symbol? (first bodies)) (first bodies))
        bodies       (if (symbol? (first bodies)) (rest bodies) bodies)
        bodies       (if (vector? (first bodies)) (list bodies) bodies)
        bodies       (doall (map expand-fn-body bodies))]
    (if (nil? name)
      (cons f bodies)
      (cons f (cons name bodies)))))

(defn- expand-deftype
  "Handle deftype* forms."
  [[symbol typename classname fields implements interfaces & methods]]
  (assert (= implements :implements))
  (let [expanded-methods (doall (map #(expand-args % 2) methods))]
    (concat
     (list symbol typename classname fields implements interfaces)
     expanded-methods)))

(defn- expand-reify
  "Handle reify* forms."
  [[symbol interfaces & methods]]
  (let [expanded-methods (map #(expand-args % 2) methods)]
    (cons symbol (cons interfaces expanded-methods))))

; Handlers for special forms that require special treatment. The default
; is expand-args.
(def ^{:private true} special-form-handlers
  {'quote         identity
   'var           identity
   'def           #(expand-args % 2)
   'new           #(expand-args % 2)
   'let*          expand-with-bindings
   'letfn*        expand-with-bindings
   'loop*         expand-with-bindings
   'fn*           expand-fn
   'deftype*      expand-deftype
   'reify*        expand-reify})

(defn- expand-list
  "Recursively expand a form that is a list or a cons."
  [form]
  (let [f (first form)]
    (if (symbol? f)
      (if (contains? special-forms f)
        ((get special-form-handlers f expand-args) form)
        (expand-args form))
      (doall (map expand-all form)))))

(defn- expand-all
  "Expand a form recursively."
  [form]
  (let [exp (expand form)]
    (cond (symbol? exp) exp
          (seq? exp) (expand-list exp)
          (vector? exp) (into [] (map expand-all exp))
          (map? exp) (into {} (map expand-all (seq exp)))
          :else exp)))

(defn- check-not-qualified
  "Verify that none of the supplied symbols are namespace-qualified"
  [symbols]
  (when (not-every? nil? (map namespace symbols))
    (throw (Exception.
            (str "Can't macrolet qualified symbol(s): "
                 (clojure.string/join ", "
                                      (map str (filter namespace symbols)))))))
  symbols)

(defmacro macrolet
  "Define local macros that are used in the expansion of exprs. The
   syntax is the same as for letfn forms."
  [fn-bindings & exprs]
  (let [names      (check-not-qualified (map first fn-bindings))
        name-map   (into {} (map (fn [n] [(list 'quote n) n]) names))
        macro-map  (eval `(letfn ~fn-bindings ~name-map))]
    (binding [macro-fns     (merge macro-fns macro-map)
              macro-symbols (apply dissoc macro-symbols names)]
      `(do ~@(doall (map expand-all exprs))))))

(defmacro symbol-macrolet
  "Define local symbol macros that are used in the expansion of exprs.
   The syntax is the same as for let forms."
  [symbol-bindings & exprs]
  (let [symbol-map (into {} (map vec (partition 2 symbol-bindings)))
        names      (check-not-qualified (keys symbol-map))]
    (binding [macro-fns     (apply dissoc macro-fns names)
              macro-symbols (merge macro-symbols symbol-map)]
      `(do ~@(doall (map expand-all exprs))))))

(defmacro defsymbolmacro
  "Define a symbol macro. Because symbol macros are not part of
   Clojure's built-in macro expansion system, they can be used only
   inside a with-symbol-macros form."
  [symbol expansion]
  (let [meta-map (if (meta symbol) (meta symbol) {})
        meta-map (assoc meta-map :symbol-macro true)]
  `(def ~(with-meta symbol meta-map) (quote ~expansion))))

(defmacro with-symbol-macros
  "Fully expand exprs, including symbol macros."
  [& exprs]
  `(do ~@(doall (map expand-all exprs))))

(defmacro deftemplate
  "Define a macro that expands into forms after replacing the
   symbols in params (a vector) by the corresponding parameters
   given in the macro call."
  [name params & forms]
  (let [param-map (for [p params] (list (list 'quote p) (gensym)))
        template-params (vec (map second param-map))
        param-map (vec (apply concat param-map))
        expansion (list 'list (list 'quote `symbol-macrolet) param-map
                        (list 'quote (cons 'do forms)))]
    `(defmacro ~name ~template-params ~expansion)))

(defn mexpand-1
  "Like clojure.core/macroexpand-1, but takes into account symbol macros."
  [form]
  (binding [macro-fns {}
            macro-symbols {}
            protected-symbols #{}]
    (expand-1 form)))

(defn mexpand
  "Like clojure.core/macroexpand, but takes into account symbol macros."
  [form]
  (binding [macro-fns {}
            macro-symbols {}
            protected-symbols #{}]
    (expand form)))

(defn mexpand-all
  "Perform a full recursive macro expansion of a form."
  [form]
  (binding [macro-fns {}
            macro-symbols {}
            protected-symbols #{}]
    (expand-all form)))

(defn name-with-attributes
  "To be used in macro definitions.
   Handles optional docstrings and attribute maps for a name to be defined
   in a list of macro arguments. If the first macro argument is a string,
   it is added as a docstring to name and removed from the macro argument
   list. If afterwards the first macro argument is a map, its entries are
   added to the name's metadata map and the map is removed from the
   macro argument list. The return value is a vector containing the name
   with its extended metadata map and the list of unprocessed macro
   arguments."
  [name macro-args]
  (let [[docstring macro-args] (if (string? (first macro-args))
                                 [(first macro-args) (next macro-args)]
                                 [nil macro-args])
    [attr macro-args]          (if (map? (first macro-args))
                                 [(first macro-args) (next macro-args)]
                                 [{} macro-args])
    attr                       (if docstring
                                 (assoc attr :doc docstring)
                                 attr)
    attr                       (if (meta name)
                                 (conj (meta name) attr)
                                 attr)]
    [(with-meta name attr) macro-args]))


;; copied from https://github.com/clojure/algo.monads/blob/master/src/main/clojure/clojure/algo/monads.clj

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Defining monads
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro monad
  "Define a monad by defining the monad operations. The definitions
   are written like bindings to the monad operations m-bind and
   m-result (required) and m-zero and m-plus (optional)."
  [operations]
  `(let [~'m-bind   ::undefined
         ~'m-result ::undefined
         ~'m-zero   ::undefined
         ~'m-plus   ::undefined
         ~@operations]
     {:m-result ~'m-result
      :m-bind ~'m-bind 
      :m-zero ~'m-zero
      :m-plus ~'m-plus}))

(defmacro defmonad
  "Define a named monad by defining the monad operations. The definitions
   are written like bindings to the monad operations m-bind and
   m-result (required) and m-zero and m-plus (optional)."

  ([name doc-string operations]
   (let [doc-name (with-meta name {:doc doc-string})]
     `(defmonad ~doc-name ~operations)))

  ([name operations]
   `(def ~name (monad ~operations))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Using monads
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- ensure-items [n steps]
  "Ensures there are at least n elements on a list, will fill up with nil
  values when list is not big enough."
  (take n (concat steps (repeat nil))))

(defn- each3-steps [steps]
  "Transforms a list in a list of triples following the form:
   [a b c] => [[a b c] [b c nil] [c nil nil]]."
  (let [n (count steps)]
  (map vector (ensure-items n steps)
              (ensure-items n (rest steps))
              (ensure-items n (rest (rest steps))))))

(def ^:private prepare-monadic-steps
     #(->> % (partition 2) reverse each3-steps))

(defn- if-then-else-statement
  "Process an :if :then :else steps when adding a new
  monadic step to the mexrp."
  [[[_          else-mexpr]
    [then-bform then-mexpr]
    [if-bform   if-conditional]] mexpr continuation]
    (cond
      (and (identical? then-bform :then)
           (identical? if-bform   :if))
        `(if ~if-conditional
          ~(reduce continuation
                   mexpr
                   (prepare-monadic-steps then-mexpr))
          ~(reduce continuation
                   mexpr
                   (prepare-monadic-steps else-mexpr)))
      :else
       (throw (Exception. "invalid :if without :then and :else"))))

(defn- merge-cond-branches [cond-branches]
  (let [merger (fn [result cond-branch]
                  (-> result
                      (conj (first cond-branch))
                      (conj (second cond-branch))))]
    (reduce merger [] cond-branches)))

(defn cond-statement
  "Process a :cond steps when adding a new monadic step to the mexrp."
  [expr mexpr continuation]
  (let [cond-sexps (partition 2 expr)
        result (for [[cond-sexp monadic-sexp] cond-sexps]
                     (list cond-sexp
                           (reduce continuation
                                   mexpr
                                   (prepare-monadic-steps monadic-sexp))))]
      `(cond ~@(merge-cond-branches result))))

(defn- add-monad-step
  "Add a monad comprehension step before the already transformed
   monad comprehension expression mexpr."
  [mexpr steps]
  (let [[[bform expr :as step] & _] steps]
    (cond
      (identical? bform :when)  `(if ~expr ~mexpr ~'m-zero)
      (identical? bform :let)   `(let ~expr ~mexpr)
      (identical? bform :cond)  (cond-statement expr mexpr add-monad-step)
      (identical? bform :then)  mexpr
      ; ^ ignore :then step (processed on the :else step)
      (identical? bform :if)    mexpr
      ; ^ ignore :if step (processed on the :else step)
      (identical? bform :else)
        (if-then-else-statement steps mexpr add-monad-step)
      :else
        (list 'm-bind expr (list 'fn [bform] mexpr)))))

(defn- monad-expr
  "Transforms a monad comprehension, consisting of a list of steps
   and an expression defining the final value, into an expression
   chaining together the steps using :bind and returning the final value
   using :result. The steps are given as a vector of
   binding-variable/monadic-expression pairs."
  [steps expr]
  (when (odd? (count steps))
    (throw (Exception. "Odd number of elements in monad comprehension steps")))

  (let [rsteps  (prepare-monadic-steps steps)
        [[lr ls] & _] (first rsteps)]
    (if (= lr expr)
      ; Optimization: if the result expression is equal to the result
      ; of the last computation step, we can eliminate an m-bind to
      ; m-result.
      (reduce add-monad-step
        ls
        (rest rsteps))
      ; The general case.
      (reduce add-monad-step
        (list 'm-result expr)
        rsteps))))

(defmacro with-monad
  "Evaluates an expression after replacing the keywords defining the
   monad operations by the functions associated with these keywords
   in the monad definition given by name."
  [monad & exprs]
  `(let [name#      ~monad
         ~'m-bind   (:m-bind name#)
         ~'m-result (:m-result name#)
         ~'m-zero   (:m-zero name#)
         ~'m-plus   (:m-plus name#)]
     (with-symbol-macros ~@exprs)))

(defmacro domonad
  "Monad comprehension. Takes the name of a monad, a vector of steps
   given as binding-form/monadic-expression pairs, and a result value
   specified by expr. The monadic-expression terms can use the binding
   variables of the previous steps.
   If the monad contains a definition of m-zero, the step list can also
   contain conditions of the form :when p, where the predicate p can
   contain the binding variables from all previous steps.
   A clause of the form :let [binding-form expr ...], where the bindings
   are given as a vector as for the use in let, establishes additional
   bindings that can be used in the following steps."
  ([steps expr]
    (monad-expr steps expr))
  ([name steps expr]
    (let [mexpr (monad-expr steps expr)]
      `(with-monad ~name ~mexpr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Defining functions used with monads
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro defmonadfn
  "Like defn, but for functions that use monad operations and are used inside
   a with-monad block."
  {:arglists '([name docstring? attr-map? args expr]
               [name docstring? attr-map? (args expr) ...])}
  [name & options]
  (let [[name options]  (name-with-attributes name options)
        fn-name (symbol (str *ns*) (format "m+%s+m" (str name)))
        make-fn-body    (fn [args expr]
                          (list (vec (concat ['m-bind 'm-result
                                              'm-zero 'm-plus] args))
                                (list `with-symbol-macros expr)))]
    (if (list? (first options))
      ; multiple arities
      (let [arglists        (map first options)
            exprs           (map second options)
            ]
        `(do
           (defsymbolmacro ~name (partial ~fn-name ~'m-bind ~'m-result 
                                                   ~'m-zero ~'m-plus))
           (defn ~fn-name ~@(map make-fn-body arglists exprs))))
      ; single arity
      (let [[args expr] options]
        `(do
           (defsymbolmacro ~name (partial ~fn-name ~'m-bind ~'m-result 
                                                   ~'m-zero ~'m-plus))
           (defn ~fn-name ~@(make-fn-body args expr)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Commonly used monad functions
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Define the four basic monad operations as symbol macros that
; expand to their unqualified symbol equivalents. This makes it possible
; to use them inside macro templates without having to quote them.
(defsymbolmacro m-result m-result)
(defsymbolmacro m-bind m-bind)
(defsymbolmacro m-zero m-zero)
(defsymbolmacro m-plus m-plus)

(defmacro m-lift
  "Converts a function f of n arguments into a function of n
  monadic arguments returning a monadic value."
  [n f]
  (let [expr (take n (repeatedly #(gensym "x_")))
        vars (vec (take n (repeatedly #(gensym "mv_"))))
        steps (vec (interleave expr vars))]
    (list `fn vars (monad-expr steps (cons f expr)))))

(defmonadfn m-join
  "Converts a monadic value containing a monadic value into a 'simple'
   monadic value."
  [m]
  (m-bind m identity))

(defmonadfn m-fmap
  "Bind the monadic value m to the function returning (f x) for argument x"
  [f m]
  (m-bind m (fn [x] (m-result (f x)))))

(defmonadfn m-seq
  "'Executes' the monadic values in ms and returns a sequence of the
   basic values contained in them."
  [ms]
  (reduce (fn [q p]
            (m-bind p (fn [x]
                        (m-bind q (fn [y]
                                    (m-result (cons x y)))) )))
          (m-result '())
          (reverse ms)))

(defmonadfn m-map
  "'Executes' the sequence of monadic values resulting from mapping
   f onto the values xs. f must return a monadic value."
  [f xs]
  (m-seq (map f xs)))

(defmonadfn m-chain
  "Chains together monadic computation steps that are each functions
   of one parameter. Each step is called with the result of the previous
   step as its argument. (m-chain (step1 step2)) is equivalent to
   (fn [x] (domonad [r1 (step1 x) r2 (step2 r1)] r2))."
  [steps]
  (reduce (fn m-chain-link [chain-expr step]
            (fn [v] (m-bind (chain-expr v) step)))
          m-result
          steps))

(defmonadfn m-reduce
  "Return the reduction of (m-lift 2 f) over the list of monadic values mvs
   with initial value (m-result val)."
  ([f mvs]
   (if (empty? mvs)
     (m-result (f))
     (let [m-f (m-lift 2 f)]
       (reduce m-f mvs))))
  ([f val mvs]
   (let [m-f    (m-lift 2 f)
         m-val  (m-result val)]
     (reduce m-f m-val mvs))))

(defmonadfn m-until
  "While (p x) is false, replace x by the value returned by the
   monadic computation (f x). Return (m-result x) for the first
   x for which (p x) is true."
  [p f x]
  (if (p x)
    (m-result x)
    (domonad
      [y (f x)
       z (m-until p f y)]
      z)))

(defmacro m-when
  "If test is logical true, return monadic value m-expr, else return
   (m-result nil)."
  [test m-expr]
  `(if ~test ~m-expr (~'m-result nil)))

(defmacro m-when-not
  "If test if logical false, return monadic value m-expr, else return
   (m-result nil)."
  [test m-expr]
  `(if ~test (~'m-result nil) ~m-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Utility functions used in monad definitions
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn- flatten*
  "Like #(apply concat %), but fully lazy: it evaluates each sublist
   only when it is needed."
  [ss]
  (lazy-seq
   (when-let [s (seq ss)]
     (concat (first s) (flatten* (rest s))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Commonly used monads
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identity monad
(defmonad identity-m
   "Monad describing plain computations. This monad does in fact nothing
    at all. It is useful for testing, for combination with monad
    transformers, and for code that is parameterized with a monad."
  [m-result identity
   m-bind   (fn m-result-id [mv f]
              (f mv))
  ])

; Maybe monad
(defmonad maybe-m
   "Monad describing computations with possible failures. Failure is
    represented by nil, any other value is considered valid. As soon as
    a step returns nil, the whole computation will yield nil as well."
   [m-zero   nil
    m-result (fn m-result-maybe [v] v)
    m-bind   (fn m-bind-maybe [mv f]
               (if (nil? mv) nil (f mv)))
    m-plus   (fn m-plus-maybe [& mvs]
               (first (drop-while nil? mvs)))
    ])

; Sequence monad (called "list monad" in Haskell)
(defmonad sequence-m
   "Monad describing multi-valued computations, i.e. computations
    that can yield multiple values. Any object implementing the seq
    protocol can be used as a monadic value."
   [m-result (fn m-result-sequence [v]
               (list v))
    m-bind   (fn m-bind-sequence [mv f]
               (flatten* (map f mv)))
    m-zero   (list)
    m-plus   (fn m-plus-sequence [& mvs]
               (flatten* mvs))
    ])

; Set monad
(defmonad set-m
   "Monad describing multi-valued computations, like sequence-m,
    but returning sets of results instead of sequences of results."
   [m-result (fn m-result-set [v]
               #{v})
    m-bind   (fn m-bind-set [mv f]
               (apply clojure.set/union (map f mv)))
    m-zero   #{}
    m-plus   (fn m-plus-set [& mvs]
               (apply clojure.set/union mvs))
    ])

; State monad
(defmonad state-m
   "Monad describing stateful computations. The monadic values have the
    structure (fn [old-state] [result new-state])."
   [m-result  (fn m-result-state [v]
                (fn [s] [v s]))
    m-bind    (fn m-bind-state [mv f]
                (fn [s]
                  (let [[v ss] (mv s)]
                    ((f v) ss))))
   ])

(defn update-state
  "Return a state-monad function that replaces the current state by the
   result of f applied to the current state and that returns the old state."
  [f]
  (fn [s] [s (f s)]))

(defn set-state
  "Return a state-monad function that replaces the current state by s and
   returns the previous state."
  [s]
  (update-state (fn [_] s)))

(defn fetch-state
  "Return a state-monad function that returns the current state and does not
   modify it."
  []
  (update-state identity))

(defn fetch-val
  "Return a state-monad function that assumes the state to be a map and
   returns the value corresponding to the given key. The state is not modified."
  [key]
  (fn [s] [(get s key ) s]))

(defn update-val
  "Return a state-monad function that assumes the state to be a map and
   replaces the value associated with the given key by the return value
   of f applied to the old value. The old value is returned."
  [key f]
  (fn [s]
    (let [old-val (get s key)
          new-s   (assoc s key (f old-val))]
      [old-val new-s])))

(defn set-val
  "Return a state-monad function that assumes the state to be a map and
   replaces the value associated with key by val. The old value is returned."
  [key val]
  (update-val key (fn [_] val)))

(defn with-state-field
  "Returns a state-monad function that expects a map as its state and
   runs statement (another state-monad function) on the state defined by
   the map entry corresponding to key. The map entry is updated with the
   new state returned by statement."
  [key statement]
  (fn [s]
    (let [substate (get s key nil)
          [result new-substate] (statement substate)
          new-state (assoc s key new-substate)]
      [result new-state])))

(defn state-m-until
  "An optimized implementation of m-until for the state monad that
   replaces recursion by a loop."
  [p f x]
  (letfn [(until [p f x s]
            (if (p x)
              [x s]
              (let [[x s] ((f x) s)]
                (recur p f x s))))]
    (fn [s] (until p f x s))))

; Writer monad
(defprotocol writer-monad-protocol
  "Accumulation of values into containers"
  (writer-m-add [container value]
  "add value to container, return new container")
  (writer-m-combine [container1 container2]
  "combine two containers, return new container"))

(extend-protocol writer-monad-protocol

  clojure.lang.IPersistentVector
  (writer-m-add [c v] (conj c v))
  (writer-m-combine [c1 c2] (vec (concat c1 c2)))

  clojure.lang.IPersistentList
  (writer-m-add [c v] (conj c v))
  (writer-m-combine [c1 c2] (concat c1 c2))

  clojure.lang.APersistentSet
  (writer-m-add [c v] (conj c v))
  (writer-m-combine [c1 c2] (clojure.set/union c1 c2))

  java.lang.String
  (writer-m-add [c v] (str c v))
  (writer-m-combine [c1 c2] (str c1 c2)))

(defn writer-m
  "Monad describing computations that accumulate data on the side, e.g. for
   logging. The monadic values have the structure [value log]. Any of the
   accumulators from clojure.contrib.accumulators can be used for storing the
   log data. Its empty value is passed as a parameter."
  [empty-accumulator]
  (monad
   [m-result  (fn m-result-writer [v]
                [v empty-accumulator])
    m-bind    (fn m-bind-writer [mv f]
                (let [[v1 a1] mv
                      [v2 a2] (f v1)]
                  [v2 (writer-m-combine a1 a2)]))
    ]))

(defmonadfn write [v]
  (let [[_ a] (m-result nil)]
    [nil (writer-m-add a v)]))

(defn listen [mv]
  (let [[v a] mv] [[v a] a]))

(defn censor [f mv]
  (let [[v a] mv] [v (f a)]))

; Continuation monad

(defmonad cont-m
  "Monad describing computations in continuation-passing style. The monadic
   values are functions that are called with a single argument representing
   the continuation of the computation, to which they pass their result."
  [m-result   (fn m-result-cont [v]
                (fn [c] (c v)))
   m-bind     (fn m-bind-cont [mv f]
                (fn [c]
                  (mv (fn [v] ((f v) c)))))
   ])

(defn run-cont
  "Execute the computation c in the cont monad and return its result."
  [c]
  (c identity))

(defn call-cc
  "A computation in the cont monad that calls function f with a single
   argument representing the current continuation. The function f should
   return a continuation (which becomes the return value of call-cc),
   or call the passed-in current continuation to terminate."
  [f]
  (fn [c]
    (let [cc (fn cc [a] (fn [_] (c a)))
          rc (f cc)]
      (rc c))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Monad transformers
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro monad-transformer
  "Define a monad transforer in terms of the monad operations and the base
   monad. The argument which-m-plus chooses if m-zero and m-plus are taken
   from the base monad or from the transformer."
  [base which-m-plus operations]
  `(let [which-m-plus# (cond (= ~which-m-plus :m-plus-default)
                               (if (= ::undefined (with-monad ~base ~'m-plus))
                                 :m-plus-from-transformer
                                 :m-plus-from-base)
                             (or (= ~which-m-plus :m-plus-from-base)
                                 (= ~which-m-plus :m-plus-from-transformer))
                               ~which-m-plus
                             :else
                               (throw (java.lang.IllegalArgumentException.
                                       "undefined m-plus choice")))
         combined-monad# (monad ~operations)]
    (if (= which-m-plus# :m-plus-from-base)
      (assoc combined-monad#
        :m-zero (with-monad ~base ~'m-zero)
        :m-plus (with-monad ~base ~'m-plus))
      combined-monad#)))

(defn maybe-t
  "Monad transformer that transforms a monad m into a monad in which
   the base values can be invalid (represented by nothing, which defaults
   to nil). The third argument chooses if m-zero and m-plus are inherited
   from the base monad (use :m-plus-from-base) or adopt maybe-like
   behaviour (use :m-plus-from-transformer). The default is :m-plus-from-base
   if the base monad m has a definition for m-plus, and
   :m-plus-from-transformer otherwise."
  ([m] (maybe-t m nil :m-plus-default))
  ([m nothing] (maybe-t m nothing :m-plus-default))
  ([m nothing which-m-plus]
   (monad-transformer m which-m-plus
     [m-result (with-monad m m-result)
      m-bind   (with-monad m
                 (fn m-bind-maybe-t [mv f]
                   (m-bind mv
                           (fn [x]
                             (if (identical? x nothing)
                               (m-result nothing)
                               (f x))))))
      m-zero   (with-monad m (m-result nothing))
      m-plus   (with-monad m
                 (fn m-plus-maybe-t [& mvs]
                   (if (empty? mvs)
                     (m-result nothing)
                     (m-bind (first mvs)
                             (fn [v]
                               (if (= v nothing)
                                 (apply m-plus-maybe-t (rest mvs))
                                 (m-result v)))))))
      ])))

(defn sequence-t
  "Monad transformer that transforms a monad m into a monad in which
   the base values are sequences. The argument which-m-plus chooses
   if m-zero and m-plus are inherited from the base monad
   (use :m-plus-from-base) or adopt sequence-like
   behaviour (use :m-plus-from-transformer). The default is :m-plus-from-base
   if the base monad m has a definition for m-plus, and
   :m-plus-from-transformer otherwise."
  ([m] (sequence-t m :m-plus-default))
  ([m which-m-plus]
   (monad-transformer m which-m-plus
     [m-result (with-monad m
                 (fn m-result-sequence-t [v]
                   (m-result (list v))))
      m-bind   (with-monad m
                 (fn m-bind-sequence-t [mv f]
                   (m-bind mv
                           (fn [xs]
                             (m-fmap flatten*
                                     (m-map f xs))))))
      m-zero   (with-monad m (m-result (list)))
      m-plus   (with-monad m
                 (fn m-plus-sequence-t [& mvs]
                   (m-reduce concat (list) mvs)))
      ])))

;; Contributed by Jim Duey
(defn state-t
  "Monad transformer that transforms a monad m into a monad of stateful
  computations that have the base monad type as their result."
  [m]
  (monad [m-result (with-monad m
                     (fn m-result-state-t [v]
                       (fn [s]
                         (m-result [v s]))))
          m-bind   (with-monad m
                     (fn m-bind-state-t [stm f]
                       (fn [s]
                         (m-bind (stm s)
                                 (fn [[v ss]]
                                   ((f v) ss))))))
          m-zero   (with-monad m
                     (if (= ::undefined m-zero)
                       ::undefined
                       (fn [s]
                         m-zero)))
          m-plus   (with-monad m
                     (if (= ::undefined m-plus)
                       ::undefined
                       (fn [& stms]
                         (fn [s]
                           (apply m-plus (map #(% s) stms))))))
          ]))
