 #lang racket
(require redex)

; Grammar
(define-language System_C
  (e x
     0
     1
     true
     false
     (box b))
  
  (b f
     (#\{ (x: \tau) ... (f: \sigma) ... => s #\}) ; Not sure on the syntax of the =>, it may need to be a literal
     (unbox e)
     (l cap)) ; Operational Semantics
  
  (s (def f = b #\; s)
     (b #\( e ... b ... #\))
     (val x = s)
     (return e)
     (try #\{ f => s #\} with #\{ (x ... #\, k) => s #\})
     (l #\{ s #\} with #\{ (x ... k) => s #\})) ; Operational Semantics
  
  (\tau Int
        Boolean
        (\sigma at C))
  
  (\sigma ((\tau ... #\, (f: \sigma) ... ) \rightarrow \tau))
  
  (C \emptyset
     (#\{ f #\})
     (C \cup C)
     (#\{ l #\})) ; Operational Semantics
  
  (\Gamma \emptyset
     (\Gamma #\, x : \tau)
     (\Gamma #\, f : \star \sigma)
     (\Gamma #\, f : C \sigma))

  ; Evaluation Context for Contexts
  (E ::= hole
     (#\{ val x = E #\; s #\})
     (l #\{ E #\} with #\{ (x ... k) => s #\})) ; Not sure the parentheses need to be there for the x ... k. Don't  think they actually add anything of real substance

  ; Evaluation Contexts for Delimited Contexts
  ; We need to include the l and l' difference
  ; Not sure about the syntax of the tagging of H with l
  (l H ::= hole
     (val x = l H #\; s) ; I am not 100% on the syntax of the #\;. From what I understand, the #\ is just a literal character
     (l #\{ l H #\} with #\{ (x ... k) => s #\}))
  )


; Typing Rules
(define-judgment-form System_C
  #:mode (typeof I I I I O)
  #:contract (typeof \Gamma #\: \sigma \tau C)

  [(typeof \Gamma f #\: \sigma C) ; Need to include logic about the tracking. This is not a correct definition of transparent
   ------------------------------ "Transparent"
   (typeof \Gamma f #\: \sigma C)]

  [(typeof \Gamma f #\: \sigma C)
   ------------------------------ "Tracked"
   (typeof \Gamma f #\: \sigma f)]

  [(typeof (\Gamma #\, (x : \tau)) s #\: f C) ; Figure our how to do the arrow typing things
   ------------------------------ "Block"
   (typeof \Gamma s #\: ((\tau_i ... #\, (f: \sigma) ... ) \rightarrow \tau) f)]

  [(typeof \Gamma e #\: \sigma C) ; Not sure exactly what we should do when there are things which don't exactl fit into our mode (e.g., \sigma at C)
   ------------------------------ "BoxElim"
   (typeof \Gamma (unbox e) #\: \sigma C)]

  [(typeof \Gamma b #\: \sigma C) ; Not sure how to articulate subset (probably have to define a metafunction or something). Replace C by C_prime after figuring out how to do subsetting
   ------------------------------ "BSub"
   (typeof \Gamma b #\: \sigma C)]

  [
   ------------------------------ "Lit"
   (typeof \Gamma n #\: \Int \emptyset)] ; Not sure if the emptyset is the best way to represent the lack of a C or just C. Check in the paper if there not being a C is a shorthand for the emtpyset. Just C throws an unbound variable error though.

  [(typeof \Gamma x #\: \tau \emptyset) ; Once again, have to figure out how to represent an element being within a set. I imagine that it will be a metafunction
   ------------------------------ "Var"
   (typeof \Gamma x #\: \tau \emptyset)]

  [(typeof \Gamma b #\: \sigma C)
   ------------------------------ "BoxIntro"
   (typeof \Gamma (box b) #\: \sigma C)]

  [(typeof \Gamma s_0 #\: \tau_1 C_0)                      ; \tau_0 unbound variable
   (typeof (\Gamma #\, x : \tau_1) s_0 #\: \tau_1 C_1)     ; (\Gamma #\, x : \tau_0) unbound variable error
   ------------------------------ "Val"
   (typeof \Gamma (val x = s_0 #\; s_1) #\: \tau_1 (C_0 \cup C_1))]

  [(typeof \Gamma e #\: \tau C)         ; Same problem as with C. Need to figure out if the C should be C or an emptyset
   ------------------------------ "Ret"
   (typeof \Gamma (return e) #\: \tau \emptyset)]

  ; [(typeof \Gamma f #\: \sigma C)
  ;  ------------------------------ "App"
  ; (typeof \Gamma f #\: \sigma f)]

  ; Figure out how to resolve variable unbound
  ; [(typeof \Gamma b #\: \sigma C_prime)
  ; (typeof (\Gamma #\, f : C_prime \sigma) b #\: \tau C)
  ; ------------------------------ "Def"
  ; (typeof \Gamma (def f = b #\; s) #\: \tau C)]

  [(typeof \Gamma s #\: \tau C)          ; Similar problem with C_prime and subsets
   ------------------------------ "SSub"
   (typeof \Gamma s #\: \tau C)]

  [(typeof \Gamma s_1 #\: \tau (C \cup #\{ f #\}))      ; (\Gamma #\, f : \star (\tau_i ... \rightarrow \tau_0)) is throwing an error because \tau_1 isn't bound
   (typeof \Gamma s_2 #\: \tau C)                       ; Once again, this gamme will have to be tinkered around with and figured out
   ------------------------------ "Try"
   (typeof \Gamma (try #\{ f => s_1 #\} with #\{ (x ... #\, k) => s_2 #\} ) #\: \tau C)])

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

   (--> (#\{ (x ... f ...) => s #\} (v ... w ...))
        (substitute* s [x v] [f C] [f w])) ; Not sure how to include the where or how to do the substitution with many variables

   (--> (try #\{ f => s #\} with #\{ (x ... k) => s_prime #\}) ; Not sure if that is how primes are done
        (l #\{ substitute* s [f #\{ l #\}] [f l cap] #\} with #\{ (x... k) => s_prime #\})) ; Elipses are wrong but throwing datum: no pattern variables before ellipsis in template
   
   ))