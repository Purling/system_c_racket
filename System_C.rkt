 #lang racket
(require redex)

;; Symbols for use Γ, σ, τ, →, ⇒, Ξ, Σ
;; N.B.: Handy for debugging (parameterize ([current-traced-metafunctions '(statement-type find find-helper find-equal block-type expr-type subset)]) (judgment-holds ...))

;; Grammar
(define-language System_C
  (e x
     ()
     natural
     true
     false
     (box b)
     (new e)
     (! e)
     (e := e)
     (l))

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
     (intercept f ⇒ s with h)
     (l s with h))

  (τ Int
     Boolean
     (σ at C)
     (Ref τ))
  
  (σ (τ ... #\, (f : σ) ... → τ))

  (C (f-or-l ...))

  (Γ (g ...))

  (Σ ((l : τ) ...))

  (Ξ ((l : τ) ...)
     ((l : v) ...))

  (g (x : τ)
     (f :* σ)
     (f : C σ)
     (k : C σ)
     (l : τ ... → τ))

  (c none
     C)

  (x variable-not-otherwise-mentioned)

  (f variable-not-otherwise-mentioned)

  (f-or-l f
          l)

  (k variable-not-otherwise-mentioned)

  (l variable-not-otherwise-mentioned)

  (h ((x : τ) ... #\, (k : τ) ⇒ s))

  (xfl x
       f
       l)

  (find-return-type (C σ)
                    (* σ)
                    τ
                    #f
                    (τ ... → τ))

  (E hole
     (Γ E)
     (E (e ... #\, b ...))
     (val x = E #\; s)
     (l E with (x ... #\, k) ⇒ s))

  #:binding-forms
  (def f = b #\; s #:refers-to f)
  (val x = s #\; s #:refers-to x)
  (try f ⇒ s with h #:refers-to f) #;
  ((x : τ) ... #\, (f : σ) ... ⇒ s #:refers-to (shadow (shadow x ...) (shadow f ...)))
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
   (side-condition (equal? (term xfl) (term x)))]

  [(find-helper xfl (f :* σ))
   (* σ)
   (side-condition (equal? (term xfl) (term f)))]

  [(find-helper xfl (f : C σ))
   (C σ)
   (side-condition (equal? (term xfl) (term f)))]

  [(find-helper xfl (l : τ_1 ... → τ_0))
   (τ_1 ... → τ_0)
   (side-condition (equal? (term xfl) (term l)))]
)

;; Metafunction which detects if the key x-or-f is the same as found within the term g
(define-metafunction System_C
  find-equal : xfl g -> boolean
  [(find-equal xfl (x : τ))
   #t
   (side-condition (equal? (term xfl) (term x)))

   or

   #f]

  [(find-equal xfl (f :* σ))
   #t
   (side-condition (equal? (term xfl) (term f)))

   or

   #f]

  [(find-equal xfl (f : C σ))
   #t
   (side-condition (equal? (term xfl) (term f)))

   or

   #f]

  [(find-equal xfl (l : τ_1 ... → τ_0))
   #t
   (side-condition (equal? (term xfl) (term l)))

   or

   #f]
)

;; Metafunction which attempts to find an element within a list and either returns #f or the element found
(define-metafunction System_C
  find : xfl Γ -> find-return-type
  [(find xfl (g_1 g_2 ...))
   (find-helper xfl g_1)
   (where #t (find-equal xfl g_1))

   or

   (find xfl (g_2 ...))]
  
  [(find xfl ())
   #f]
  )

;; Set append metafunction for one element
(define-metafunction System_C
  append : f c -> c
  [(append f (f_1 ... f f_2 ...))
   (f_1 ... f f_2 ...)]

  [(append f (f_1 ...))
   (f_1 ... f)]

  [(append f none)
   none]
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

  [(flatten ())
   ()]
  )

;; Typing rules for block typing
(define-judgment-form System_C
  #:contract (block-type Γ Σ b σ c C)
  #:mode (block-type I I I O I O)

  [(where (C σ) (find f Γ))
   (where #t (subset C c))
   ------------------------ "Transparent"
   (block-type Γ Σ f σ c C)]

  [(where (* σ) (find f Γ))
   (where #t (subset (f) c))
   ------------------------- "Tracked"
   (block-type Γ Σ f σ c (f))]

  [(statement-type (g ... (x : τ_1) ... (f_1 :* σ) ...) Σ s τ (set-append c (f_1 ...)) C)
   (where #t (subset C (set-append c (f_1 ...))))
   --------------------------------------------------------------------------------------------------------------- "Block"
   (block-type (g ...) Σ ((x : τ_1) ... #\, (f_1 : σ) ... ⇒ s) (τ_1 ... #\, (f_1 : σ) ... → τ) c (set-minus (f_1 ...) C))]

  [(expr-type Γ Σ e (σ at C))
   (where #t (subset C c))
   ------------------------------- "BoxElim"
   (block-type Γ Σ (unbox e) σ c C)]
  )

;; Typing rule for expression typing
(define-judgment-form System_C
  #:mode (expr-type I I I O)
  #:contract (expr-type Γ Σ e τ)

  [
   --------------------------- "Lit"
   (expr-type Γ Σ natural Int)]

  [(where τ (find x Γ))
   -------------------- "Var"
   (expr-type Γ Σ x τ)]

  [(block-type Γ Σ b σ none C)
   ------------------------------- "BoxIntro"
   (expr-type Γ Σ (box b) (σ at C))]

  [(expr-type Γ Σ e (Ref τ))
   ------------------------------- "Deref"
   (expr-type Γ Σ (! e) τ)]

  [(expr-type Γ Σ e τ)
   ------------------------------- "New"
   (expr-type Γ Σ (new e) (Ref τ))]

  [(expr-type Γ Σ e_1 (Ref τ))
   (expr-type Γ Σ e_2 τ)
   ------------------------------- "Assign"
   (expr-type Γ Σ (e_1 := e_2) τ)]

  [(where τ (find l Σ))
   ------------------------------- "Ref"
   (expr-type Γ Σ l (Ref τ))]
  )

(define-judgment-form System_C
  #:mode (statement-type I I I O I O)
  #:contract (statement-type Γ Σ s τ c C)

  [(statement-type (g ...) Σ s_0 τ_0 c C_0)
   (statement-type (g ... (x : τ_0)) Σ s_1 τ_1 c C_1)
   (where #t (subset C_0 c))
   (where #t (subset C_1 c))
   -------------------------------------------------------------------------- "Val"
   (statement-type (g ...) Σ (val x = s_0 #\; s_1) τ_1 c (set-append C_0 C_1))]

  [(expr-type Γ Σ e τ)
   ------------------------------------- "Ret"
   (statement-type Γ Σ (return e) τ c ())]

  [(block-type Γ Σ b (τ_1 ... #\, (f : σ_1) ... → τ) c C)
   (expr-type Γ Σ e_1 τ_1) ...
   (block-type Γ Σ b_1 σ_1 c C_1) ...
   (where #t (subset C c))
   (where (#t ...) ((subset C_1 c) ... ))
    ------------------------------------------------------------------------------------------------------------ "App"
   (statement-type Γ Σ (b (e_1 ... #\, b_1 ...)) (substitute τ [f C_1] ...) c (set-append (flatten (C_1 ...)) C))]

  [(block-type (g ...) Σ b σ c C_prime)
   (statement-type (g ... (f : C_prime σ)) Σ s τ c C)
   (where #t (subset C_prime c))
   (where #t (subset C c))
   ------------------------------------------------- "Def"
   (statement-type (g ...) Σ (def f = b #\; s) τ c C)]

  [(statement-type (g ... (f :* (τ_1 ... #\, → τ_0))) Σ s_1 τ (append f c) C)
   (statement-type (g ... (x_1 : τ_1) ... (k : C (τ_0 #\, → τ))) Σ s_2 τ c C)
   (where #t (subset C (append f c)))
   --------------------------------------------------------------------------------------------------------- "Try"
   (statement-type (g ...) Σ (try f ⇒ s_1 with ((x_1 : τ_1) ... #\, (k : τ_0) ⇒ s_2)) τ c (set-minus (f) C))]

  [(where (τ_1 ... → τ_0) (find l Γ))
   (where #t (subset (l) c))
   ----------------------------------------------------- "Cap"
   (statement-type Γ Σ (cap l) (τ_1 ... #\, → τ_0) c (l))]

  [(where (τ_1 ... → τ_0) (find l (g ...)))
   (statement-type (g ...) Σ s_1 τ (append l c) C)
   (statement-type (g ... (x_1 : τ_1) ... (k : C (τ_0 → τ))) Σ s_2 τ c C)
   (where #t (subset C (append l c)))
   ----------------------------------------------------- "Reset"
   (statement-type (g ...) Σ (l s_1 with ((x_1 : τ_1) ... #\, (k : τ_0) ⇒ s_2)) τ c (set-minus (l) C))]

  [(statement-type (g ... (f :* (τ_1 ... #\, → τ_0))) Σ s_1 τ (append f c) C)
   (statement-type (g ... (x_1 : τ_1) ... (k : C (τ_0 #\, → τ))) Σ s_2 τ c C)
   (where #t (subset C (append f c)))
   (where (τ_1 ... #\, → τ_0) (find-equal f (g ...)))
   --------------------------------------------------------------------------------------------------------- "Intercept"
   (statement-type (g ...) Σ (try f ⇒ s_1 with ((x_1 : τ_1) ... #\, (k : τ_0) ⇒ s_2)) τ c (set-minus (f) C))]

  [(statement-type (g ...) Σ s_1 τ c C)
   (statement-type (g ... (x_1 : τ_1) ... (k : C (τ_0 #\, → τ))) Σ s_2 τ c C)
   (where (τ_1 ... #\, → τ_0) (find-equal l Σ))
   --------------------------------------------------------------------------------------------------------- "CapIntercept"
   (statement-type (g ...) Σ (try (cap l) ⇒ s_1 with ((x_1 : τ_1) ... #\, (k : τ_0) ⇒ s_2)) τ c C)]
  )

(define-judgment-form System_C
  #:mode (multi-block I O O)
  #:contract (multi-block (w ...) (σ ...) (C ...))

  [(block-type () () w σ none C) ...
   ------------------------------------- "Multi"
   (multi-block (w ...) (σ ...) (C ...))
   ]
  )

;; Reduction Rules
(define reduction
  (reduction-relation
   System_C
   #:domain (Γ s) 

   (--> (in-hole E (unbox (box b)))
        (in-hole E b)
        "box")

   (--> (in-hole E (val x = (return v) #\; s))
        (in-hole E (substitute s [x v]))
        "val")

   (--> (in-hole E (def f = w #\; s))
        (in-hole E (substitute s [f w]))
        "def")

   (--> (in-hole E (l (return v) with h))
        (in-hole E (return v))
        "ret")

   (--> (in-hole E (((x_1 : τ_1) ... #\, (f_1 : σ_1) ... ⇒ s) (v_1 ... #\, w_1 ...)))
        (in-hole E (substitute s [x_1 v_1] ... [f_1 C] ... [f_1 w_1] ...))
        (judgment-holds (multi-block (w_1 ...) (σ_1 ...) (C ...)))
        "app")

   (--> ((g ...) (in-hole E (try f ⇒ s with ((x_1 : τ_1) ... #\, (k : τ_0) ⇒ s_prime))))
        ((g ... (l : τ_1 ... → τ_0)) (in-hole E (l (substitute s [(l) f] [(cap l) f]) with ((x_1 : τ_1) ... #\, (k : τ_0) ⇒ s_prime))))
        (fresh l)
        "try")

   (--> (in-hole E (l (in-hole E_1 ((cap l) (v_1 ... #\, ))) with ((x_1 : τ_1) ... #\, (k : τ_0) ⇒ s)))
        (in-hole E (substitute s [x_1 v_1] ... [k ((x : τ_0) #\, ⇒ (l (in-hole E_1 (return x)) with ((x_1 : τ_1) ... #\, (k : τ_0) ⇒ s)))]))
        (fresh x)
        "cap")

   (--> (in-hole E (! l))
        (in-hole E v)
        "deref")

   (--> (in-hole E (l := v))
        (in-hole E v)
        "assign")

   (--> (in-hole E (new v))
        (in-hole E l)
        (fresh l)
        "new")

   (--> (in-hole E (intercept (cap l) ⇒ s with ((x_1 : τ_1) ... #\, (k : τ_0) ⇒ s_prime)))
        (in-hole E (l with ((x_1 : τ_1) ... #\, (k : τ_0) ⇒ s_prime)))
        (fresh l)
        "interc")
   )
  )