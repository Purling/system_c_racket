# Positive Unit Tests

| Code    | Typing Tests | Reduction Tests | Expected Output |
| --------------- | ------- | ----- | ---- |
| `return (box ( #\, ⇒ (return 0)))`  | `(judgment-holds (statement-type () (return (box ( #\, ⇒ (return 0)))) τ none C))` | `(apply-reduction-relation reduction (term (return (box ( #\, ⇒ (return 0))))))` | `#t` <br> τ = `(#\, → Int) at ()` |
| `return 0` | `(judgment-holds (statement-type () (return 0) τ none C))` | `(apply-reduction-relation reduction (term (return 0)))` | `#t`; τ = `Int` |
| `unbox (box ( #\, ⇒ (return 0)))` | `(judgment-holds (block-type () (unbox (box ( #\, ⇒ (return 0)))) σ none C))` | `(apply-reduction-relation reduction (term (unbox (box ( #\, ⇒ (return 0))))))` | `#t` <br> σ = `(#\, → Int)`|
| `def block = ( #\, ⇒ (return 0)) #\; return (box block)` | `(judgment-holds (statement-type () (def block = ( #\, ⇒ (return 0)) #\; (return (box block))) τ none C))` | `(apply-reduction-relation reduction (term (def block = ( #\, ⇒ (return 0)) #\; (return (box block)))))` | `#t` <br> τ = `(#\, → Int) at ()` |
| `box (unbox (box (( #\, ⇒ (return 0)))))` | `(judgment-holds (expr-type () (box (unbox (box ( #\, ⇒ (return 0))))) τ))` | `(apply-reduction-relation reduction (term (box (unbox (box (( #\, ⇒ (return 0))))))))` | `#t` <br> τ = `(#\, → Int) at ()` |
| `def ret = ( #\, ⇒ (return 0)) #\; (return 1)` | `(judgment-holds (statement-type () (def ret = ( #\, ⇒ (return 0)) #\; (return 1)) τ none C))` | `(apply-reduction-relation reduction (term (def ret = ( #\, ⇒ (return 0)) #\; (return 1))))` | `#t` <br> τ = `Int` |
| `val value = (return 1) #\; (return value)` | `(judgment-holds (statement-type () (val value = (return 1) #\; (return value)) τ none C))` | `(apply-reduction-relation reduction (term (val value = (return 1) #\; (return value))))` | `#t` <br> τ = `Int` |

# Negative Unit Tests

| Code    | Typing Tests | Reduction Tests | Expected Output |
| --------------- | ------- | ----- | ---- |
| `box (unbox 0)` | `(judgment-holds (expr-type () (box (unbox 0)) (σ at C)))` | `(apply-reduction-relation reduction (term (box (unbox 0))))` | `#f` |

*TODO: Try returning a block which is not boxed*

*TODO: Try type checking block which does not have all of its capabilities*

*TODO: Put unbox box and box unbox within a wrapper so it is able to be evaluated*