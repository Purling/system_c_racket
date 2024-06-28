 #lang racket
(require redex)

; Grammar
; Consider what syntactic sugar you want to add and what you want to remove
(define-language System_C
  (e (x)
     (0)
     (1)
     (true)
     (false)
     (box b))
  
  (b (f)
     ((x \tau) ... #\, (f \sigma) ... \Rightarrow s) ; Check if this will allow for the case in which there is actually none of one of the types
     (unbox e)
     (l cap)) ; Operational Semantics
  
  (s (def f = b #\; s)
     (b e ... #\, b ... ) ; See if the two b's are different, maybe by having an underscore?
     (val x = s #\; s)
     (return e)
     (try f \Rightarrow s with x ... #\, k \Rightarrow s) ; Check if the ellipses only applies to x
     (l s with (x ... k) \Rightarrow s )) ; Operational Semantics
  
  (\tau (Int)
        (Boolean)
        (\sigma at C))
  
  (\sigma (\tau ... #\, (f \sigma) ... \rightarrow \tau)) ; Consider adding the #\: back into the f #\: \sigma

  ; Define metafunctions which emulate the functionality of sets
  (C (null)) ; Don't know if this can be added to

  (\Gamma (null))

  (x (n)
     (g)
     (variable-not-otherwise-mentioned))

  (f variable-not-otherwise-mentioned) ; Check if this can be used twice or if it needs to be in one definition with x

  ; Evaluation Context for Contexts
  (E ::= hole
     (#\{ val x = E #\; s #\})
     (l #\{ E #\} with #\{ (x ... k) => s #\})) ; Not sure the parentheses need to be there for the x ... k. Don't  think they actually add anything of real substance
  )

; Clause to determine if every element in a list is in another list (sub list)
;count (member a) b

; Typing Rules
; Look into making the output the type instead of the context
(define-judgment-form System_C
  #:mode (typeof I I I O)
  #:contract (typeof \Gamma \sigma \tau C)

  [(typeof \Gamma f \sigma C)
   (side-condition (member \sigma \Gamma)) ; Not sure if this will hold when the element exists in the list. It will if the values are truthy. Also, not sure correct when we are binding C
   ------------------------------ "Transparent"
   (typeof \Gamma f \sigma C)]

  [(typeof \Gamma f \sigma C)
   (side-condition (member \sigma \Gamma))
   ------------------------------ "Tracked"
   (typeof \Gamma f \sigma C)]

  ; Not sure if '(g ...) is a valid way to express lists
  [(typeof (append (append (\Gamma) '((x \tau) ...)) '((g \sigma) ...)) s \tau (append (C) '(g ...))) ; Define set-append (for now, we use regular list append as placeholder)
   ------------------------------ "Block"
   (typeof \Gamma (((x \tau_i) ...) #\, ((g \sigma) ...) s) \tau C)] ; Check if I need something to distinguish the many different tau's

  [(typeof \Gamma e (\sigma at ()) C)  ; I want to do (typeof \Gamma e (\sigma at C) C) but it is giving me an unbound pattern variable error
   ----------------------------------------- "BoxElim"
   (typeof \Gamma (unbox e) \sigma C)]

  [(typeof \Gamma b \sigma C)
   ;(side-condition subset (C_prime C)) ; Create metafunction which detects for subset
   ------------------------------ "BSub"
   (typeof \Gamma b \sigma C)]

  [
   ------------------------------ "Lit"
   (typeof \Gamma n \Int \emptyset)] ; I assume that we just want any list, so it may not necessarily be accurate for it to be an \emptyset

  [(typeof \Gamma x \tau C)
   (side-condition (member x \Gamma))
   ------------------------------ "Var"
   (typeof \Gamma x \tau C)]

  [(typeof \Gamma b \sigma C)
   ------------------------------ "BoxIntro"
   (typeof \Gamma (box b) \sigma C)]

  [(typeof \Gamma s_0 \tau_1 C_0)                      ; \tau_0 unbound variable
   (typeof (\Gamma #\, x : \tau_1) s_0 \tau_1 C_1)     ; (\Gamma #\, x : \tau_0) unbound variable error
   ------------------------------ "Val"
   (typeof \Gamma (val x = s_0 #\; s_1) \tau_1 (C_0 \cup C_1))]

  [(typeof \Gamma e \tau C)         ; Same problem as with C. Need to figure out if the C should be C or an emptyset
   ------------------------------ "Ret"
   (typeof \Gamma (return e) \tau \emptyset)]

  ; [(typeof \Gamma f #\: \sigma C)
  ;  ------------------------------ "App"
  ; (typeof \Gamma f #\: \sigma f)]

  ; Figure out how to resolve variable unbound
  ; [(typeof \Gamma b #\: \sigma C_prime)
  ; (typeof (\Gamma #\, f : C_prime \sigma) b #\: \tau C)
  ; ------------------------------ "Def"
  ; (typeof \Gamma (def f = b #\; s) #\: \tau C)]

  [(typeof \Gamma s \tau C)          ; Similar problem with C_prime and subsets
   ------------------------------ "SSub"
   (typeof \Gamma s \tau C)]

  [(typeof \Gamma s_1 \tau (C \cup #\{ f #\}))      ; (\Gamma #\, f : \star (\tau_i ... \rightarrow \tau_0)) is throwing an error because \tau_1 isn't bound
   (typeof \Gamma s_2 \tau C)                       ; Once again, this gamme will have to be tinkered around with and figured out
   ------------------------------ "Try"
   (typeof \Gamma (try #\{ f => s_1 #\} with #\{ (x ... #\, k) => s_2 #\} ) \tau C)])

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