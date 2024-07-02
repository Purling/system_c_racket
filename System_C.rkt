 #lang racket
(require redex)

;; Symbols for use Γ, σ, τ, →

; Grammar
; Consider what syntactic sugar you want to add and what you want to remove
(define-language System_C
  (e x
     0
     1
     true
     false
     (box b))
  
  (b f
     ((x τ) ... #\, (f σ) ... \Rightarrow s) ; Check if this will allow for the case in which there is actually none of one of the types
     (unbox e)
     (l cap)) ; Operational Semantics
  
  (s (def f = b #\; s)
     (b e ... #\, b ... ) ; See if the two b's are different, maybe by having an underscore?
     (val x = s #\; s)
     (return e)
     (try f \Rightarrow s with x ... #\, k \Rightarrow s) ; Check if the ellipses only applies to x
     (l s with (x ... k) \Rightarrow s )) ; Operational Semantics
  
  (τ Int
     Boolean
     (σ at C))
  
  (σ (\tau ... #\, (f σ) ... \rightarrow τ)) ; Consider adding the #\: back into the f #\: \sigma

  ; Define metafunctions which emulate the functionality of sets
  (C (f ...))

  (Γ (g ...))

  (g (x : τ)
     (f :* σ)
     (f : C σ))

  (x variable-not-otherwise-mentioned)

  (f variable-not-otherwise-mentioned) ; Check if this can be used twice or if it needs to be in one definition with x

  ; Evaluation Context for Contexts
  (E ::= hole
     (#\{ val x = E #\; s #\})
     (l #\{ E #\} with #\{ (x ... k) => s #\})) ; Not sure the parentheses need to be there for the x ... k. Don't  think they actually add anything of real substance
  )

; Clause to determine if every element in a list is in another list (sub list)
; count (member a) b

;; Create a find metafunction

;; Metafunctions to help determine things

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

;; Typing rules for block typing
(define-judgment-form System_C
  #:contract (block-type Γ b σ C C)
  #:mode (block-type I I I I O)

  [(block-type Γ f σ C C)
   (side-condition (member σ Γ)) ; Not sure if this will hold when the element exists in the list. It will if the values are truthy. Also, not sure correct when we are binding C
   ------------------------------ "Transparent"
   (block-type Γ f σ C C)]

  [(where g (find (f :* σ) Γ))
   ------------------------------ "Tracked"
   (block-type Γ f σ f f)]

  ; Not sure if '(g ...) is a valid way to express lists
  [(block-type (append (append (Γ) '((x τ) ...)) '((g σ) ...)) s τ (append (C) '(g ...)) C) ; Define set-append (for now, we use regular list append as placeholder)
   ------------------------------ "Block"
   (block-type Γ (((x τ_i) ...) #\, ((g σ) ...) s) τ C C)] ; Check if I need something to distinguish the many different tau's

  [(expr-type Γ e (σ at C))
   ----------------------------------------- "BoxElim"
   (block-type Γ (unbox e) σ C C)]

  ; This condition is not algorithm. As such, it will need to be built into each of the other typing rules
  ; [(block-type Γ b σ C)
  ; ;(side-condition subset (C_prime C)) ; Create metafunction which detects for subset
  ; ------------------------------ "BSub"
  ; (block-type Γ b σ C)])
)

; Typing rule for expression typing
(define-judgment-form System_C
  #:mode (expr-type I I I)
  #:contract (expr-type Γ e τ)
  
  [
   ------------------------------ "Lit"
   (expr-type Γ n Int)] ;; TODO: Look how to force n to be an integer

  [(expr-type Γ x τ)
   (side-condition (member x Γ)) ;; TODO: Confirm that this is a correct way of making sure that the side-condition is obeyed
   ------------------------------ "Var"
   (expr-type Γ x τ)]

  [(block-type Γ b σ C C)
   ------------------------------ "BoxIntro"
   (expr-type Γ (box b) (σ at C))] ;; The C is not yet bound. This is because we need to make it bidirectional (i.e., it both requires and needs C)
  
  )


; Look into making the output the type instead of the context and also into bidirectional output and input
(define-judgment-form System_C
  #:mode (typeof I I I O)
  #:contract (typeof Γ σ τ C)

  [(typeof Γ s_0 τ_1 C_0)                      ; \tau_0 unbound variable
   (typeof (Γ #\, x : τ_1) s_0 τ_1 C_1)     ; (\Gamma #\, x : \tau_0) unbound variable error
   ------------------------------ "Val"
   (typeof Γ (val x = s_0 #\; s_1) τ_1 (C_0 \cup C_1))]

  [(typeof Γ e \tau C)         ; Same problem as with C. Need to figure out if the C should be C or an emptyset
   ------------------------------ "Ret"
   (typeof Γ (return e) \tau \emptyset)]

  ; [(typeof \Gamma f #\: \sigma C)
  ;  ------------------------------ "App"
  ; (typeof \Gamma f #\: \sigma f)]

  ; Figure out how to resolve variable unbound
  ; [(typeof Γ b #\: \sigma C_prime)
  ; (typeof (Γ #\, f : C_prime \sigma) b #\: \tau C)
  ; ------------------------------ "Def"
  ; (typeof Γ (def f = b #\; s) #\: \tau C)]

  [(typeof Γ s τ C)          ; Similar problem with C_prime and subsets
   ------------------------------ "SSub"
   (typeof Γ s τ C)]

  [(typeof Γ s_1 τ (C \cup #\{ f #\}))      ; (\Gamma #\, f : \star (\tau_i ... \rightarrow \tau_0)) is throwing an error because \tau_1 isn't bound
   (typeof Γ s_2 τ C)                       ; Once again, this gamme will have to be tinkered around with and figured out
   ------------------------------ "Try"
   (typeof Γ (try #\{ f => s_1 #\} with #\{ (x ... #\, k) => s_2 #\} ) τ C)])

; Reduction Rules
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