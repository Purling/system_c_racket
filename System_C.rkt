 #lang racket
(require redex)

;; Symbols for use Γ, σ, τ, →, ⇒, Ξ

;; TODO: Encode unit tests and things of the sort using test-judgment-holds, etc. (judgment-holds (statement-type () (return (box ( #\, ⇒ (return 0)))) τ none C) τ) and (apply-reduction-relation)
;; TODO: Add the next step as a TODO (I think it might be to add vars)

;; Grammar
(define-language System_C
  (e x
     ()
     natural
     true
     false
     (box b))

  (v natural
     ()
     true
     false
     (box w))

  (w ((x : τ) ... #\, (f : σ) ... ⇒ s)
     (cap l))
  
  (b f
     ((x : τ) ... #\, (f : σ) ... ⇒ s)
     (unbox e)
     (cap l))
  
  (s (def f = b #\; s)
     (b (e ... #\, b ...))
     (val x = s #\; s)
     (return e)
     (try f ⇒ s with h)
     (l s with h))

  (τ Int
     Boolean
     (σ at C))
  
  (σ (τ ... #\, (f : σ) ... → τ))

  (C (f-or-l ...))

  (Γ (g ...))

  (g (x : τ)
     (f :* σ)
     (f : C σ)
     (l : τ ... → τ))

  (c none
     C)

  (x variable-not-otherwise-mentioned)

  (f variable-not-otherwise-mentioned)

  (f-or-l f
          l)

  (k variable-not-otherwise-mentioned)

  ;; CHECK: https://docs.racket-lang.org/redex/Reduction_Relations.html indicates that the "Fresh variable clauses generate variables". Thus, I am pretty sure that fresh generates variables.
  (l variable)

  (h (((x : τ) ... #\, (k : τ)) ⇒ s))

  (xfl x
       f
       l)

  (find-return-type (C σ)
                    (* σ)
                    τ
                    #f
                    (τ ... → τ))

  (E hole
     (val x = E #\; s)
     (l E with (x ... #\, k) ⇒ s))

  ;; CHECK: Need to check that these binding-forms are done correctly. I am not sure that we need shadow because shadow seems to be for multiple variables in a single scope (https://docs.racket-lang.org/redex/Languages.html#(part._.Multiple_.Variables_in_a_.Single_.Scope))
  #:binding-forms
  (def f = b #\; s #:refers-to b)
  (val x = s_0 #\; s #:refers-to s_0) ;; QUESTION: Not sure if I need to differentiate the two s terms
  (try f ⇒ s with h #:refers-to s)
  ;; QUESTION: The below does not seemed to be allowed because it is throwing an error that there can only be one ellipses per binding form. It only seems to work if we put square brackets (https://docs.racket-lang.org/guide/syntax-notation.html) around one of the lists.
  ;; CONT'D: I don't know if this means that we will have to apply the square brackets to the other parts of the grammar where this term appears or if there is a better way to approach this.
  ([(x : τ) ...] #\, [(f : σ) ...] ⇒ s #:refers-to s)
  )

;; Metafunction to find whether a l is in a Ξ
(define-metafunction System_C
  find-signature : l Ξ -> boolean
  [(find-signature l ((l_1 : τ ... → τ_1) ... (l : τ_2 ... → τ_3) (l_2 : τ_4 ... → τ_5) ...))
   #t]

  [(find-signature l Ξ)
   #f]
  )

;; Metafunction which returns the type given an x-or-f (key) and a g which contains the type (value)
(define-metafunction System_C
  find-helper : xfl g -> find-return-type
  [(find-helper xfl (x : τ))
   τ
   (side-condition (= (term xfl) (term x)))]

  [(find-helper xfl (f :* σ))
   (* σ)
   (side-condition (= (term xfl) (term f)))]

  [(find-helper xfl (f : C σ))
   (C σ)
   (side-condition (= (term xfl) (term f)))]

  [(find-helper xfl (l : τ_1 ... → τ_0))
   (τ_1 ... → τ_0)
   (side-condition (= (term xfl) (term l)))]
)

;; Metafunction which detects if the key x-or-f is the same as found within the term g
(define-metafunction System_C
  find-equal : xfl g -> boolean
  [(find-equal xfl (x : τ))
   #t
   (side-condition (= (term xfl) (term x)))

   or

   #f]

  [(find-equal xfl (f :* σ))
   #t
   (side-condition (= (term xfl) (term f)))

   or

   #f]

  [(find-equal xfl (f : C σ))
   #t
   (side-condition (= (term xfl) (term f)))

   or

   #f]

  [(find-equal xfl (l : τ_1 ... → τ_0))
   #t
   (side-condition (= (term xfl) (term l)))

   or

   #f]
)

;; Metafunction which attempts to find an element within a list and either returns #f or the element found
(define-metafunction System_C
  find : xfl Γ -> find-return-type
  [(find xfl (g_1 g_2 ... g_3))
   (find-helper xfl g_1)
   (where #t (find-equal xfl g_1))

   or

   (find xfl (g_2 ... g_3))]
  
  [(find xfl (g_1 g_2))
   (find-helper xfl g_1)
   (where #t (find-equal xfl g_1))

   or

   (find xfl g_2)]
  
  [(find xfl g_1)
   (find-helper xfl g_1)
   (where #t (find-equal xfl g_1))

   or

   #f]
  )

;; Set append metafunction for one element
;; CHECK: Even though C is not (f-or-l ...) because it is only (f ...) in this metafunction, I don't think that it will require any changes for the set functions. We are not detecting for l outside of the reduction rules.
(define-metafunction System_C
  append : f C -> C
  [(append f (f_1 ... f f_2 ...))
   (f_1 ... f f_2 ...)]

  [(append f (f_1 ...))
   (f_1 ... f)]
  )

(define-metafunction System_C
  list-append : f Γ -> Γ
  [(list-append f (g ...))
   (g ... f)]
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
   ------------------------ "Transparent"
   (block-type Γ f σ c C)]

  [(where (* σ) (find f Γ))
   (where #t (subset (f) c))
   ------------------------- "Tracked"
   (block-type Γ f σ c (f))]

  ;; QUESTION: Uncertain about the (where #t (subset C c)) because it seems like it covers (where #t (subset C (set-append c (f ...))))
  ;; QUESTION: Not sure if g_j is just a f_j or something else entirely? Reading the paper, it seems that g_j is a block which is what f_j would be.
  [(statement-type (g ... (x : τ_1) ... (f_1 :* σ) ...) s τ (set-append c (f_1 ...)) C)
   (where #t (subset C (set-append c (f_1 ...))))
   (where #t (subset C c))
   --------------------------------------------------------------------------------------------------------------- "Block"
   (block-type (g ...) ((x : τ_1) ... #\, (f_1 : σ) ... ⇒ s) (τ_1 ... #\, (f_1 : σ) ... → τ) c (set-minus (f_1 ...) C))]

  [(expr-type Γ e (σ at C))
   (where #t (subset C c))
   ------------------------------- "BoxElim"
   (block-type Γ (unbox e) σ c C)]
  )

;; Typing rule for expression typing
(define-judgment-form System_C
  #:mode (expr-type I I O)
  #:contract (expr-type Γ e τ)

  [
   --------------------------- "Lit"
   (expr-type Γ natural Int)]

  [(where τ (find x Γ))
   -------------------- "Var"
   (expr-type Γ x τ)]

  [(block-type Γ b σ none C)
   ------------------------------- "BoxIntro"
   (expr-type Γ (box b) (σ at C))]
  )

(define-judgment-form System_C
  #:mode (statement-type I I O I O)
  #:contract (statement-type Γ s τ c C)

  [(statement-type (g ...) s_0 τ_0 c C_0)
   (statement-type (g ... (x : τ_0)) s_1 τ_1 c C_1)
   (where #t (subset C_0 c))
   (where #t (subset C_1 c))
   -------------------------------------------------------------------------- "Val"
   (statement-type (g ...) (val x = s_0 #\; s_1) τ_1 c (set-append C_0 C_1))]

  [(expr-type Γ e τ)
   ------------------------------------- "Ret"
   (statement-type Γ (return e) τ c ())]

  ;; QUESTION: Uncertain about the subset rule which is encoded by (where (#t ...) ((subset C_j c) ... )). Also not sure if the substitution (substitute τ [C_j f] ...) works as intended.
  [(block-type Γ b (τ_1 ... #\, (f : σ_1) ... → τ) c C)
   (expr-type Γ e_1 τ_1) ...
   (block-type Γ b_1 σ_1 c C_1) ...
   (where #t (subset C c))
   (where (#t ...) ((subset C_1 c) ... ))
    ------------------------------------------------------------------------------------------------------------ "App"
   (statement-type Γ (b (e_1 ... #\, b_1 ...)) (substitute τ [f C_1] ...) c (set-append (flatten (C_1 ...)) C))]

  [(block-type (g ...) b σ c C_prime)
   (statement-type (g ... (f : C_prime σ)) s τ c C)
   (where #t (subset C_prime c))
   (where #t (subset C c))
   ------------------------------------------------- "Def"
   (statement-type (g ...) (def f = b #\; s) τ c C)]

  ;; QUESTION: Is the inference for the continuation (k : τ) correct?
  ;; QUESTION: Uncertain about the (where #t (subset C c)) because it seems like it covers (where #t (subset C (append f c)))
  [(statement-type (g ... (f :* (τ_1 ... → τ_0))) s_1 τ (append f c) C)
   (statement-type (g ... (x_1 : τ_1) ... (k : C (τ_0 → τ))) s_2 τ c C)
   (where #t (subset C c))
   (where #t (subset C (append f c)))
   --------------------------------------------------------------------------------------------------------- "Try"
   (statement-type (g ...) (try f ⇒ s_1 with ((x_1 : τ_1) ... #\, (k : τ_0)) ⇒ s_2) τ c (set-minus (f) C))]

  [(where (τ_1 ... → τ_0) (find l Γ))
   (where #t (subset (l) c))
   ----------------------------------------------------- "Cap"
   (statement-type Γ (cap l) (τ_1 ... #\, → τ_0) c (l))]

  ;; QUESTION: Same questions as with try because they are very similar rules
  [(where (τ_1 ... → τ_0) (find l (g ...)))
   (statement-type (g ...) s_1 τ (append l c) C)
   (statement-type (g ... (x_1 : τ_1) ... (k : C (τ_0 → τ))) s_2 τ c C)
   (where #t (subset C c))
   (where #t (subset C (append l c)))
   ----------------------------------------------------- "Reset"
   (statement-type (g ...) (l s_1 with (((x_1 : τ_1) ... #\, (k : τ_0)) ⇒ s_2)) τ c (set-minus (l) C))]
  )

;; Reduction Rules
(define reduction
  (reduction-relation
   System_C
   #:domain s

   (--> (in-hole E (unbox (box b)))
        b
        "box")

   (--> (in-hole E (val x = return v #\; s))
        (substitute s [x v])
        "val")

   (--> (in-hole E (def f = w #\; s))
        (substitute s [f w])
        "def")

   (--> (in-hole E (l (return v) with h))
        v
        "ret")
   
   ;; QUESTION: This judgment-holds is not correct, but I can't seem to get it to work for lists of judgment-holds and if I try to do it using a where clause, it complains about the judgment form having output positions
   ;; QUESTION: Is this the correct way in which to express the substitution? Especially the f_j substitution.
   (--> (in-hole E (((x_1 : τ_1) ... #\, (f_1 : σ_1) ... ⇒ s) (v_1 ... #\, w_1 ...)))
        (substitute s [x_1 v_1] ... [f_1 C] ... [f_1 w_1] ...)
        (judgment-holds (block-type () (w_1 ...) (σ_1 ...) none (C ...)))
        "app")

   ;; QUESTION: Just need another set of eyes over this reduction rule and whether I have done this correctly.
   ;; QUESTION: Am I actually supposed to add the l into the Ξ here in this reduction rule? Also, not sure if the way in which I have added the l is the correct way to do this (i.e., by using the judgment-holds to get the Γ).
   (--> (in-hole E (try f ⇒ s with (((x_1 : τ_1) ... #\, (k : τ_0)) ⇒ s_prime)))
        (l (substitute s [(l) f] [(cap l) f]) with (((x_1 : τ_1) ... #\, (k : τ_0)) ⇒ s_prime))
        (fresh l)
        (judgment-holds (statement-type (list-append (l : τ_1 ... → τ_0) Γ) (try f ⇒ s with (((x_1 : τ_1) ... #\, (k : τ_0)) ⇒ s_prime)) τ none C))
        "try")

   ;; CHECK: Just want to make sure that I have done the nested in-hole correctly
   ;; QUESTION: What is 'y' and I am not sure I have represented the hole in the substitution correctly
   (--> (in-hole E (l (in-hole E_1 ((cap l) (v_1 ... #\, ))) with (((x_1 : τ_1) ... #\, (k : τ_0)) ⇒ s)))
        (substitute s [x_1 v_1] ... [k (y ⇒ l (in-hole E_1 (return y)) with (((x_1 : τ_1) ... #\, (k : τ_0)) ⇒ s))])
        "cap")
   )
  )