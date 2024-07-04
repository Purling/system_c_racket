 #lang racket
(require redex)

;; Symbols for use Γ, σ, τ, →, ⇒, Ξ

;; Grammar
(define-language System_C
  (e x
     natural
     true
     false
     (box b))
  
  (b f
     ((x : τ) ... #\, (f : σ) ... ⇒ s)
     (unbox e)
     (cap l))
  
  (s (def f = b #\; s)
     (b (e ... #\, b ...))
     (val x = s #\; s)
     (return e)
     (try f ⇒ s with ((x : τ) ... #\, (k : τ)) ⇒ s)
     (l s with ((x : τ) ... #\, (k : τ)) ⇒ s))
  
  (τ integer
     true
     false
     (σ at C))
  
  (σ (τ ... #\, (f : σ) ... → τ))

  (C (f-or-l ...))

  (Γ (g ...))

  (g (x : τ)
     (f :* σ)
     (f : C σ))

  (c none
     C)

  (x variable-not-otherwise-mentioned)

  (f variable-not-otherwise-mentioned)

  (f-or-l f
          l)

  (k variable-not-otherwise-mentioned)

  ;; SANITY CHECK: https://docs.racket-lang.org/redex/Reduction_Relations.html indicates that the "Fresh variable clauses generate variables". Thus, I am pretty sure that fresh generates variables.
  (l variable)

  (Ξ (r ...))

  (r (l : τ ... → τ))

  ;; QUESTION: I have defined a h here which is ((x : τ_i) ... #\, (k : τ)) ⇒ s because in the reduction rules, we are presented with a h and I am pretty sure that this is what h represents.
  (h ((x : τ_i) ... #\, (k : τ)) ⇒ s)

  (x-or-f x
          f)

  (find-return-type (C σ)
                    (* σ)
                    τ
                    #f)

  (E hole
     (val x = E #\; s)
     (l E with (x ... #\, k) ⇒ s))
  )

;; Metafunction which returns the type given an x-or-f (key) and a g which contains the type (value)
(define-metafunction System_C
  find-helper : x-or-f g -> find-return-type
  [(find-helper x-or-f (x : τ))
   τ
   (side-condition (= (term x-or-f) (term x)))]

  [(find-helper x-or-f (f :* σ))
   (* σ)
   (side-condition (= (term x-or-f) (term f)))]

  [(find-helper x-or-f (f : C σ))
   (C σ)
   (side-condition (= (term x-or-f) (term f)))]
)

;; Metafunction which detects if the key x-or-f is the same as found within the term g
(define-metafunction System_C
  find-equal : x-or-f g -> boolean
  [(find-equal x-or-f (x : τ))
   #t
   (side-condition (= (term x-or-f) (term x)))

   or

   #f]

  [(find-equal x-or-f (f :* σ))
   #t
   (side-condition (= (term x-or-f) (term f)))

   or

   #f]

  [(find-equal x-or-f (f : C σ))
   #t
   (side-condition (= (term x-or-f) (term f)))

   or

   #f]
)

;; Metafunction which attempts to find an element within a list and either returns #f or the element found
(define-metafunction System_C
  find : x-or-f Γ -> find-return-type
  [(find x-or-f (g_1 g_2 ... g_3))
   (find-helper x-or-f g_1)
   (where #t (find-equal x-or-f g_1))

   or

   (find x-or-f (g_2 ... g_3))]
  
  [(find x-or-f (g_1 g_2))
   (find-helper x-or-f g_1)
   (where #t (find-equal x-or-f g_1))

   or

   (find x-or-f g_2)]
  
  [(find x-or-f g_1)
   (find-helper x-or-f g_1)
   (where #t (find-equal x-or-f g_1))

   or

   #f]
  )

;; Set append metafunction for one element
;; SANITY CHECK: Even though C is not (f-or-l ...) because it is only (f ...) in this metafunction, I don't think that it will require any changes for the set functions. We are not detecting for l outside of the reduction rules.
(define-metafunction System_C
  append : f C -> C
  [(append f (f_1 ... f f_2 ...))
   (f_1 ... f f_2 ...)]

  [(append f C)
   (C f)]
  )

;; Set append for appending two sets together
(define-metafunction System_C
  set-append : c c -> c
  [(set-append (f f_1 ...) C)
   (set-append (f_1 ...) (append f C))]

  [(set-append () C)
   C]

  [(set-append none c)
   none]

  [(set-append c none)
   none]
  )

;; Subset metafunction
(define-metafunction System_C
  subset : C c -> boolean
  [(subset C none)
   #t]
  
  [(subset (f f_1 ...) (f_2 ... f f_3 ...))
   (subset (f_1 ...) (f_2 ... f f_3 ...))]

  [(subset () C)
   #t]

  [(subset C c)
   #f])

;; Set minus metafunction
(define-metafunction System_C
  set-minus : C C -> C
  [(set-minus (f f_1 ...) (f_2 ... f f_3 ...))
   (set-minus (f_1 ...) (f_2 ... f_3 ...))]

  [(set-minus (f f_1 ...) (f_2 ...))
   (set-minus (f_1 ...) (f_2 ...))]

  [(set-minus () C)
   C]

  [(set-minus C ())
   C]
  )

;; Metafunction which flattens a list of lists
(define-metafunction System_C
  flatten : (C ...) -> C
  [(flatten (C C_1 C_2 ...))
   (flatten ((set-append C C_1) C_2 ...))]

  [(flatten (C))
   C]
  )

;; Typing rules for block typing
(define-judgment-form System_C
  #:contract (block-type Γ b σ c C)
  #:mode (block-type I I O I O)

  [(where (C σ) (find f Γ))
   (where #t (subset C c))
   ---------------------------- "Transparent"
   (block-type Γ f σ c C)]

  [(where (* σ) (find f Γ))
   (where #t (subset (f) c))
   --------------------------- "Tracked"
   (block-type Γ f σ c (f))]

  ;; QUESTION: Uncertain about the (where #t (subset C c)) because it seems like it covers (where #t (subset C (set-append c (f ...))))
  [(statement-type (Γ (x : τ_i) ... (f :* σ) ...) s τ (set-append c (f ...)) C)
   (where #t (subset C (set-append c (f ...))))
   (where #t (subset C c))
   --------------------------------------------------------------------------------------------- "Block"
   (block-type Γ ((x : τ_i) ... #\, (f : σ) ... ⇒ s) (τ_i ... #\, (f : σ) ... → τ) c (set-minus (f ...) C))]

  [(expr-type Γ e (σ at C))
   (where #t (subset C c))
   ----------------------------------------- "BoxElim"
   (block-type Γ (unbox e) σ c C)]
  )

;; Typing rule for expression typing
(define-judgment-form System_C
  #:mode (expr-type I I O)
  #:contract (expr-type Γ e τ)

  [
   ------------------------------ "Lit"
   (expr-type Γ natural Int)]

  [(where τ (find x Γ))
   -------------------------- "Var"
   (expr-type Γ x τ)]

  [(block-type Γ b σ none C)
   ------------------------------- "BoxIntro"
   (expr-type Γ (box b) (σ at C))]
  )

(define-judgment-form System_C
  #:mode (statement-type I I O I O)
  #:contract (statement-type Γ σ τ c C)

  [(statement-type Γ s_0 τ_0 c C_0)
   (statement-type (Γ (x : τ_0)) s_1 τ_1 c C_1)
   (where #t (subset C_0 c))
   (where #t (subset C_1 c))
   ----------------------------------------------------------------------- "Val"
   (statement-type Γ (val x = s_0 #\; s_1) τ_1 c (set-append C_0 C_1))]

  [(expr-type Γ e τ)
   ---------------------------------------------------- "Ret"
   (statement-type Γ (return e) τ c ())]

  ;; QUESTION: Uncertain about the subset rule which is encoded by (where (#t ...) ((subset C_j c) ... )). Also not sure if the substitution (substitute τ [f C_j] ...) works as intended.
  [(block-type Γ b (τ_i ... #\, (f : σ) ... → τ) c C)
   (expr-type Γ e_i τ_i) ...
   (block-type Γ b_j σ_j c C_j) ...
   (where #t (subset C c))
   (where (#t ...) ((subset C_j c) ... ))
    -------------------------------------------------------------------------------------------------- "App"
   (statement-type Γ (b (e_i ... #\, b_j ...)) (substitute τ [C_j f] ...) c (set-append (flatten (C_j ...)) C))]

  [(block-type Γ b σ c C_prime)
   (statement-type (Γ (f : C_prime σ)) s τ c C)
   (where #t (subset C_prime c))
   (where #t (subset C c))
   -------------------------------------------- "Def"
   (statement-type Γ (def f = b #\; s) τ c C)]

  ;; QUESTION: Is the inference for the continuation (k : τ) correct?
  ;; QUESTION: Uncertain about the (where #t (subset C c)) because it seems like it covers (where #t (subset C (append f c)))
  [(statement-type (Γ (f :* (τ_i ... → τ_0))) s_1 τ (append f c) C)
   (statement-type (Γ (x_i : τ_i) ... (k : C (τ_0 → τ))) s_2 τ c C)
   (where #t (subset C c))
   (where #t (subset C (append f c)))
   ------------------------------------------------------------------------------------ "Try"
   (statement-type Γ (try f ⇒ s_1 with ((x_i : τ_i) ... #\, (k : τ_0)) ⇒ s_2) τ c (set-minus (f) C))]
  )

;; Reduction Rules
;; TODO: Use either gensym or fresh to generate unique runtime labels (this would be for try blocks). If using gensym, use pattern for defining l in the grammar otherwise, fresh will require something else
(define reduction
  ;; TODO: Determine if a 'domain' tag is necessary
  (reduction-relation System_C

   ;; SANITY CHECK: Does the in-hole make sense. The way I have understood it, the in-hole is a way of defining the evaluation contexts.
   (--> (in-hole E (val x = E_1 #\; s))
        (in-hole E E_1))

   (--> (in-hole E (l E_1 with (x ... #\, k) ⇒ s))
        (in-hole E E_1))

   (--> (unbox (box b))
        b
        "box")

   ;; TODO: Check if I have to define a binding forms in order for substitute to work properly
   (--> (val x = return e #\; s)
        (substitute s [x e])
        "val")

   (--> (def f = b #\; s)
        (substitute s [f b])
        "def")

   (--> (l (return e) with h)
        e
        "ret")

   ;; QUESTION: Not entirely sure how to encode the 'where' clause of the rule. As a result, the substitution is supposed to be (substitute s [e x] ... [C f] ... [b f] ...) but I have removed the [C f] because C does not exist.
   (--> (((x : τ) ... #\, (f : σ) ⇒ s) (e ... #\, b ...))
        (substitute s [e x] ... [b f] ...)
        "app")

   ;; TODO: Generate a new l (either using fresh or gensym) and put it in the place of the l
   ;; TODO: Add the where clause
   (--> (try f ⇒ s with ((x : τ_i) ... #\, (k : τ)) ⇒ s_prime)
        (l (substitute s [(l) f] [(cap l) f]) with ((x : τ_i) ... #\, (k : τ)) ⇒ s_prime)
        "try")

   ;; TODO: Figure out how to represent the cap reduction rule
   ;(--> (in-hole E (l (E_1) with h))
   ;     (in-hole E E_1)
   ;     "cap")
   
   ))