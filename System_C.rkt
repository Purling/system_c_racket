 #lang racket
(require redex)

;; Symbols for use Γ, σ, τ, →, ⇒

;; Grammar
(define-language System_C
  (e x
     0
     1
     true
     false
     (box b))
  
  (b f
     ((x : τ) ... #\, (f : σ) ... ⇒ s) ;; TODO: Check if this will allow for the case in which there is actually none of one of the types. Or, check if it will be necessary to check for no types. Also, check if there will need to be brackets around the list
     (unbox e)
     (l cap)) ;; QUESTION: Do we actually need these operational semantics here or should we extend them elsewhere?
  
  (s (def f = b #\; s)
     (b (e ... #\, b ...)) ;; QUESTION: Are the two 'b's present different? If not, I will probably need an underscore or something to differentiate
     (val x = s #\; s)
     (return e)
     (try f ⇒ s with (x ... #\, k) ⇒ s) ;; QUESTION: Do the ellipses only apply to x
     (l s with (x ... k) ⇒ s ))
  
  (τ Int
     Boolean
     (σ at C))
  
  (σ (τ ... #\, (f : σ) ... → τ))

  (C (f ...))

  (Γ (g ...))

  (g (x : τ)
     (f :* σ)
     (f : C σ))

  (x variable-not-otherwise-mentioned)

  (f variable-not-otherwise-mentioned)

  (E ::= hole
     (#\{ val x = E #\; s #\})
     (l #\{ E #\} with #\{ (x ... k) => s #\})) ;; QUESTION: Not sure the parentheses need to be there for the x ... k. Don't  think they actually add anything of real substance
  )

;; Metafunction which attempts to find an element within a list and either returns #f or the element found
(define-metafunction System_C
  find : g Γ -> g
  [(find g (g_1 g_2 ... g_3))
   g
   (side-condition (= (term g) (term g_1)))

   or

   (find g (g_2 ... g_3))]
  
  [(find g (g_1 g_2))
   g
   (side-condition (= (term g) (term g_1)))

   or

   (find g g_2)]
  
  [(find g g_1)
   g
   (side-condition (= (term g) (term g_1)))

   or

   #f]
  )

;; Set append metafunction for one element
(define-metafunction System_C
  append : f C -> C
  [(append f (f_1 ... f f_2 ...))
   (f_1 ... f f_2 ...)]

  [(append f (f f_2 ...))
   (f f_2 ...)]

  [(append f (f_2 ... f))
   (f_2 ... f)]

  [(append f C)
   (C f)]
  )

;; Set append for appending two sets together
(define-metafunction System_C
  set-append : C C -> C
  [(set-append (f f_1 ...) C)
   (set-append (f_1 ...) (append f C))]

  [(set-append (f) C)
   (append f C)]
  )

;; Subset metafunction
(define-metafunction System_C
  subset : C C -> C         ;; TODO: Look into if this has to be a maybe type (optional type) or something similar for the output. The output should be a bool, but we have yet to define a #f and #t in our language.
  [(subset (f f_1 ...) (f_2 ... f f_4 ...))
   (subset (f_1 ...) (f_2 ... f f_4 ...))

   or

   #f]
  
  [(subset (f f_1 ...) (f f_2 ...))
   (subset (f_1 ...) (f f_2 ...))

   or

   #f]

  [(subset (f f_1 ...) (f_2 ... f))
   (subset (f_1 ...) (f_2 ... f))

   or

   #f]

  [(subset (f) (f_1 ... f f_2 ...))
   #t

   or

   #f]
  
  [(subset (f) (f f_1 ...))
   #t
   
   or

   #f]

  [(subset (f) (f_1 ... f))
   #t

   or

   #f])

;; TODO: Figure out how exactly substitution would work

;; Typing rules for block typing
(define-judgment-form System_C
  #:contract (block-type Γ b σ C C) ;; QUESTION: Is this the way in which we would do bi-directional input and output? I have done so naively.
  #:mode (block-type I I I I O)

  [(where g (find (f : C σ) Γ))
   ---------------------------- "Transparent"
   (block-type Γ f σ C C)]

  [(where g (find (f :* σ) Γ))
   --------------------------- "Tracked"
   (block-type Γ f σ (f) (f))] ;; QUESTION: Not sure if the (f) need to be '(f) (i.e., taken out)

  ;; QUESTION: Is this the right way to express the terms with arrows on top?
  [(statement-type (Γ ((x : τ_i) ...) ((f :* σ) ...)) s τ (C (f ...)) (C (f ...)))
   --------------------------------------------------------------------------------------------- "Block"
   (block-type Γ (((x : τ_i) ...) #\, ((f : σ) ...) ⇒ s) ((τ_i ...) #\, ((f : σ) ...) → τ) C C)] ;; TODO: Check if I need something to distinguish the many different tau's. Check if the parentheses are necessary around the (x : τ_i) ... and (f : σ) ...)

  [(expr-type Γ e (σ at C))
   ----------------------------------------- "BoxElim"
   (block-type Γ (unbox e) σ C C)]
)

;; Typing rule for expression typing
(define-judgment-form System_C
  #:mode (expr-type I I I) ;; QUESTION: I think that the mode for expr-type can just be all inputs
  #:contract (expr-type Γ e τ)
  
  [(where #t (exact-integer? e)) ;; QUESTION: We may have to escape to Racket to perform this operation?
   ------------------------------ "Lit"
   (expr-type Γ e Int)]

  [(where g (find (x : τ) Γ))
   -------------------------- "Var"
   (expr-type Γ x τ)]

  [(block-type Γ b σ C C)
   ------------------------------- "BoxIntro"
   (expr-type Γ (box b) (σ at C))]
  
  )

;; TODO: Define substitution for statement typing

(define-judgment-form System_C
  #:mode (statement-type I I I I O)
  #:contract (statement-type Γ σ τ C C)

  ;; TODO: Create an append metafunction for sets
  ;; TODO: Fix problem with unbound variable
  ;; QUESTION: For the union, can we just call the metafunction which does a set union between the two sets given?
  ;[(statement-type Γ s_0 τ_0 C_0 C_0)
  ; (statement-type (Γ (x : τ_0)) s_1 τ_1 C_1 C_1)
  ; --------------------------------------------------------------------------- "Val"
  ; (statement-type Γ (val x = s_0 #\; s_1) τ_1 (set-append C_0 C_1) (set-append C_0 C_1))]

  ;; TODO: Make sure that the emptyset is expressed correctly as a null set. (i.e., I don't think it should be expressed as \emptyset. Instead, it should probably be an empty list)
  [(expr-type Γ e τ)
   ---------------------------------------------------- "Ret"
   (statement-type Γ (return e) τ \emptyset \emptyset)]

  ;; QUESTION: How do I express the multiple (expr-type Γ e_i τ_i) and (block-type b_j σ_j C_j)?
  ;; TODO: Figure out the substitution in App for (τ[f_j→C_j])
  ;; RESOLVE: Once again, input and output needs to be resolved
  ;[(block-type Γ b ((τ_i ...) #\, ((f : σ) ...) → τ) C C)
  ; (expr-type Γ e_i τ_i)
  ; (block-type Γ b_j σ_j C_j C_j)
  ;  ----------------------------------------------------- "App"
  ; (statement-type Γ (b (e_i ... #\, b_j ...)) (τ) (set-append C (C_j ...)) (set-append C (C_j ...)))]

  ;; TODO: Confirm logic around the input and output for def
  ;[(block-type Γ b σ C C_prime)  ;; QUESTION: Confirm logic of the output and input in this instance. (i.e., the typing rule is given C and we output a C_prime)
  ; (statement-type (Γ (f : C_prime σ)) b τ C C) ;; QUESTION: I still have to wrap my head around the redex and racket stuff. Is (Γ (f : C_prime σ)) a list?
  ; ------------------------------------------------ "Def"
  ; (statement-type Γ (def f = b #\; s) τ C C)]

  ;; RESOLVE: Input/Output
  ;; TODO: Make sure of the logic behind (C f). Do I need to use the append metafunction?
  ;[(statement-type (Γ (f :* (τ_i ...) → τ_0)) s_1 τ (C f) (C f))
  ; (statement-type (Γ ((x_i : τ_i) ...) (x_k : C (τ_0 → τ))) s_2 τ C C)
  ; ------------------------------------------------------------------------------------ "Try"
  ; (statement-type Γ (try f ⇒ s_1 with (x_i ... #\, x_k) ⇒ s_2) τ C C)]
  )

;; Reduction Rules
(define red
  (reduction-relation System_C ; I sometimes see a domain tag, I am not sure what exactly it is referring to or what it means

   ;(--> (in-hole E (unbox box b)) ; Add in-hole. But, it's complaining that the in-hole may match more than one context at once
   ;     (b))
   
   (--> ((unbox box b)) ; Add in-hole. But, it's complaining that the in-hole may match more than one context at once
        (b))

   (--> (val x = return v #\; s)
        (substitute s [x v])) ; May have to define binding forms in order for substitute to work properly

   (--> (def f = w #\; s)
        (substitute s [f w])) ; Make sure that the substitute parameters are given the right way (i.e., [f w] or [w f])

   (--> (l #\{ return v #\} with h)
        (v))

   ;(--> (#\{ (x ... f ...) => s #\} (v ... w ...))
   ;     (substitute* s [x v] [f C] [f w])) ; Not sure how to include the where or how to do the substitution with many variables

   (--> (try #\{ f => s #\} with #\{ (x ... k) => s_prime #\}) ; Not sure if that is how primes are done
        (l #\{ substitute* s [f #\{ l #\}] [f l cap] #\} with #\{ (x... k) => s_prime #\})) ; Elipses are wrong but throwing datum: no pattern variables before ellipsis in template
   
   ))