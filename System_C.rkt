 #lang racket
(require redex)

;; Symbols for use Γ, σ, τ, →, ⇒

;; Grammar
;; TODO: Add the operational semantics to the grammar
(define-language System_C
  (e x
     natural
     true
     false
     (box b))
  
  (b f
     ((x : τ) ... #\, (f : σ) ... ⇒ s) ;; TODO: Check if this will allow for the case in which there is actually none of one of the types. Or, check if it will be necessary to check for no types. Also, check if there will need to be brackets around the list
     (unbox e)
     (l cap))
  
  (s (def f = b #\; s)
     (b (e ... #\, b ...))
     (val x = s #\; s)
     (return e)
     (try f ⇒ s with (x ... #\, k) ⇒ s)
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

  (c none
     C)

  (x variable-not-otherwise-mentioned)

  (f variable-not-otherwise-mentioned)

  (k variable-not-otherwise-mentioned)

  (x-or-f x
          f)

  (find-return-type (C σ)
                    (* σ)
                    τ
                    #f)

  ;; TODO: Use either gensym or fresh to generate unique runtime labels (this would be for try blocks). If using gensym, use pattern for defining l in the grammar otherwise, fresh will require something else

  ;; TODO: Think about the run-time label l
  (E ::= hole
     (val x = E #\; s)
     (l E with (x ... #\, k) ⇒ s))
  )

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
;; TODO: Extend this so that the 'superset' is 'unknown'
;; TODO: Put as where clause in block typing and statement typing
(define-metafunction System_C
  subset : C C -> boolean
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
;; TODO: Make sure that the input and output is correct and works correctly

;; Typing rules for block typing
(define-judgment-form System_C
  #:contract (block-type Γ b σ c C)
  #:mode (block-type I I O I O)

  [(where (C σ) (find f Γ))
   ---------------------------- "Transparent"
   (block-type Γ f σ none C)]

  [(where (* σ) (find f Γ))
   --------------------------- "Tracked"
   (block-type Γ f σ none (f))]

  ;; QUESTION: Is this the right way to express the terms with arrows on top?
  ;; SANITY-CHECK: Confirm that g_j is an f
  ;; QUESTION: Is there a correct way in which I should be expressing the τ_i's? Is essence, each i is an identifier for a specific τ, so would it matter?
  ;; TODO: Check if I need something to distinguish the many different τ's. Check if the parentheses are necessary around the ((x : τ_i) ...) and ((f : σ) ...)
  ;; TODO: Create a 'c' append which if given a #f, just returns a #f otherwise it returns the appended
  ;; TODO: Make sure that the output 'C' has all f's removed
  ;; TODO: Make sure that the result of the appending is a superset using the subset function
  [(statement-type (Γ ((x : τ_i) ...) ((f :* σ) ...)) s τ none (C f ...))
   --------------------------------------------------------------------------------------------- "Block"
   (block-type Γ (((x : τ_i) ...) #\, ((f : σ) ...) ⇒ s) ((τ_i ...) #\, ((f : σ) ...) → τ) c C)]

  [(expr-type Γ e (σ at C))
   ----------------------------------------- "BoxElim"
   (block-type Γ (unbox e) σ C C)]
)

;; Typing rule for expression typing
(define-judgment-form System_C
  #:mode (expr-type I I O)
  #:contract (expr-type Γ e τ)

  [
   ------------------------------ "Lit"
   (expr-type Γ natural Int)]

  ;; N.B.: We should treat Γ as a lookup dictionary and use the key x to find τ
  ;; TODO: Change the find metafunction such that it returns either a found type τ or a default value (probably something like #f)
  [(where τ (find x Γ))
   -------------------------- "Var"
   (expr-type Γ x τ)]

  ;; TODO: Create a special value which indicates that we don't know what the C value is
  [(block-type Γ b σ none C)
   ------------------------------- "BoxIntro"
   (expr-type Γ (box b) (σ at C))]
  
  )

;; TODO: Define subset for statement typing

(define-judgment-form System_C
  #:mode (statement-type I I O I O)
  #:contract (statement-type Γ σ τ c C)

  ;; QUESTION: Is the 'none' correct here? My logic is that, we are getting the C_0 and C_1 from the two statement-type's and these are then given to the output (set-append C_0 C_1)
  [(statement-type Γ s_0 τ_0 none C_0)
   (statement-type (Γ (x : τ_0)) s_1 τ_1 none C_1)
   ----------------------------------------------------------------------- "Val"
   (statement-type Γ (val x = s_0 #\; s_1) τ_1 none (set-append C_0 C_1))]

  ;; TODO: Make sure that the emptyset is expressed correctly as a null set. (i.e., I don't think it should be expressed as \emptyset. Instead, it should probably be an empty list)
  [(expr-type Γ e τ)
   ---------------------------------------------------- "Ret"
   (statement-type Γ (return e) τ \emptyset \emptyset)]

  ;; QUESTION: Have I expressed the multiple of the (expr-type Γ e_i τ_i) and (block-type Γ b_j σ_j C_j C_j) correctly? (i.e., (expr-type Γ e_i τ_i) ... and (block-type Γ b_j σ_j C_j C_j) ...)
  ;; TODO: Figure out the substitution in App for (τ[f_j→C_j]). This will probably just be a redex metafunction or something of the sort.
  [(block-type Γ b (τ_i ... #\, (f : σ) ... → τ) C C)
   (expr-type Γ e_i τ_i) ...
   (block-type Γ b_j σ_j C_j C_j) ...
    -------------------------------------------------------------------------------------------------- "App"
   (statement-type Γ (b (e_i ... #\, b_j ...)) (τ) (set-append C (C_j ...)) (set-append C (C_j ...)))]

  [(block-type Γ b σ none C_prime)
   (statement-type (Γ (f : C_prime σ)) s τ C_prime C)
   -------------------------------------------- "Def"
   (statement-type Γ (def f = b #\; s) τ none C)]

  ;; RESOLVE: Input/Output problem with τ_i
  ;[(statement-type (Γ (f :* (τ_i ... → τ_0))) s_1 τ C (append f C))
  ; (statement-type (Γ (x_i : τ_i) ... (k : C (τ_0 → τ))) s_2 τ C C)
  ; ------------------------------------------------------------------------------------ "Try"
  ; (statement-type Γ (try f ⇒ s_1 with (x_i ... #\, x_k) ⇒ s_2) τ C C)]
  )

;; Reduction Rules
(define reduction
  ;; TODO: Determine if a 'domain' tag is necessary
  (reduction-relation System_C

   ;(--> (in-hole E (unbox box b)) ; Add in-hole. But, it's complaining that the in-hole may match more than one context at once
   ;     (b))
   
   (--> ((unbox box b)) ; Add in-hole. But, it's complaining that the in-hole may match more than one context at once
        (b))

   (--> (val x = return v #\; s)
        (substitute s [x v])) ; May have to define binding forms in order for substitute to work properly

   (--> (def f = w #\; s)
        (substitute s [f w])) ; Make sure that the substitute parameters are given the right way (i.e., [f w] or [w f])

   (--> (l (return v) with h)
        (v))

   ;(--> (#\{ (x ... f ...) => s #\} (v ... w ...))
   ;     (substitute* s [x v] [f C] [f w])) ; Not sure how to include the where or how to do the substitution with many variables

   (--> (try #\{ f => s #\} with #\{ (x ... k) => s_prime #\}) ; Not sure if that is how primes are done
        (l #\{ substitute* s [f #\{ l #\}] [f l cap] #\} with #\{ (x... k) => s_prime #\})) ; Elipses are wrong but throwing datum: no pattern variables before ellipsis in template
   
   ))