# Positive Unit Tests

| Code | Typing Tests | Reduction Tests | Expected Output |
| ---- | ------------ | --------------- | --------------- |
| `return (box ( #\, ⇒ (return 0)))`  | `(judgment-holds (statement-type () (return (box ( #\, ⇒ (return 0)))) τ none C))` | `(apply-reduction-relation reduction (term (() (return (box ( #\, ⇒ (return 0)))))))` | `#t` <br> τ = `(#\, → Int) at ()` |
| `return 0` | `(judgment-holds (statement-type () (return 0) τ none C))` | `(apply-reduction-relation reduction (term (() (return 0))))` | `#t`; τ = `Int` |
| `def f = (unbox (box ( #\, ⇒ (return 0)))) #\; (return (box f))` | `(judgment-holds (statement-type () (def f = (unbox (box ( #\, ⇒ (return 0)))) #\; (return (box f))) τ none C))` | `(apply-reduction-relation reduction (term (() (unbox (box ( #\, ⇒ (return 0)))))))` | `#t` <br> σ = `(#\, → Int)`|
| `def block = ( #\, ⇒ (return 0)) #\; return (box block)` | `(judgment-holds (statement-type () (def block = ( #\, ⇒ (return 0)) #\; (return (box block))) τ none C))` | `(apply-reduction-relation reduction (term (() (def block = ( #\, ⇒ (return 0)) #\; (return (box block))))))` | `#t` <br> τ = `(#\, → Int) at ()` |
| `val boxed = (return (box (unbox (box ( #\, ⇒ (return 0)))))) #\; (return boxed)` | `(judgment-holds (statement-type () (val boxed = (return (box (unbox (box ( #\, ⇒ (return 0)))))) #\; (return boxed)) τ none C))` | `(apply-reduction-relation reduction (term (() (val boxed = (return (box (unbox (box ( #\, ⇒ (return 0)))))) #\; (return boxed)))))` | `#t` <br> τ = `(#\, → Int) at ()` |
| `def ret = ( #\, ⇒ (return 0)) #\; (return 1)` | `(judgment-holds (statement-type () (def ret = ( #\, ⇒ (return 0)) #\; (return 1)) τ none C))` | `(apply-reduction-relation reduction (term (() (def ret = ( #\, ⇒ (return 0)) #\; (return 1)))))` | `#t` <br> τ = `Int` |
| `val value = (return 1) #\; (return value)` | `(judgment-holds (statement-type () (val value = (return 1) #\; (return value)) τ none C))` | `(apply-reduction-relation reduction (term (() (val value = (return 1) #\; (return value)))))` | `#t` <br> τ = `Int` |
| `try f ⇒ (return (box ( #\, ⇒ (val g = (return (box f)) #\; (return 42))))) with ( #\, (k : Int) ⇒ (return (box ( #\, ⇒ (return 0)))))` | `(judgment-holds (statement-type () (try f ⇒ (return (box ( #\, ⇒ (val g = (return (box f)) #\; (return 42))))) with ( #\, (k : Int) ⇒ (return (box ( #\, ⇒ (return 0)))))) τ none C))` | `(apply-reduction-relation reduction (term (() (try f ⇒ (return (box ( #\, ⇒ (val g = (return (box f)) #\; (return 42))))) with ( #\, (k : Int) ⇒ (return (box ( #\, ⇒ (return 0)))))))))` | `#t` <br> τ = `(#\, → Int) at ()` |
| `def f = ( #\, ⇒ (return 0)) #\; (f ( #\, ))` | `(judgment-holds (statement-type () (def f = ( #\, ⇒ (return 0)) #\; (f ( #\, ))) τ none C))` | `(apply-reduction-relation reduction (term (() (def f = ( #\, ⇒ (return 0)) #\; (f ( #\, ))))))` | `#t` <br> τ = `Int` <br> Step = `(() ((#\, ⇒ (return 0)) (#\,)))` |

# Negative Unit Tests

| Code | Typing Tests | Reduction Tests | Failing Reason |
| ---- | ------------ | --------------- | -------------- |
| `box (unbox 0)` | `(judgment-holds (expr-type () (box (unbox 0)) (σ at C)))` | `(apply-reduction-relation reduction (term (box (unbox 0))))` | Cannot unbox something which is not a block. |
| `return unknown` | `(judgment-holds (statement-type () (return unknown) τ none C))` | `(apply-reduction-relation reduction (term (return unknown)))` | `x` is not defined. |
| `return (return 0)` | `(judgment-holds (statement-type () (return (return 0)) τ none C))` | `(apply-reduction-relation reduction (term (return (return 0))))` | The syntax for return is incorrect. |
| `try f ⇒ (return (box ( #\, ⇒ (val g = (return (box f)) #\; (return 42))))) with ( #\, (k : Int) ⇒ (return 0))` | `(judgment-holds (statement-type () (try f ⇒ (return (box ( #\, ⇒ (val g = (return (box f)) #\; (return 42))))) with ( #\, (k : Int) ⇒ (return 0))) τ none C))` | `(apply-reduction-relation reduction (term (try f ⇒ (return (box ( #\, ⇒ (val g = (return (box f)) #\; (return 42))))) with ( #\, (k : Int) ⇒ (return 0)))))` | Continuation is not well-typed. |

* Try type checking block which does not have all of its capabilities

* Try type checking block with input arguments

* Put unbox box and box unbox within a wrapper so it is able to be evaluated

* Think about an example where a box (unbox (box b)) would be reduced

* val x = …; (unbox x)([], [unbox x])

* Application where there is an unbox box at front of the application

* try f => return f with ... === try { (f : 𝜎) ⇒ return box {f} f } with { ... }

* Try with return continuation