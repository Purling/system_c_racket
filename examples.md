# Safe Blocks
`def return_0 = (() ⇒ (return 0)) #\; return 1`

# Unsafe Boxing and Unboxing

## Unboxing
`unbox (return 1)`

`unbox (val one = return 1 #\; return 2)`

### Type

`unbox Int`

### Environment

`unbox ()`

`unbox (1 : Int)`

# Safe Statements

`val var_x = return 1 \#; return var_x`

# Positive Unit Tests

| Code    | Typing Tests | Reduction Tests | Expected Output |
| --------------- | ------- | ----- | ---- |
| `return (box ( #\, ⇒ (return 0)))`  | `(judgment-holds (statement-type () (return (box ( #\, ⇒ (return 0)))) τ none C))` | `(apply-reduction-relation reduction (term (return (box ( #\, ⇒ (return 0))))))` | `#t`; τ = `(#\, → Int) at ()` |
| `return 0` | `(judgment-holds (statement-type () (return 0) τ none C))` | `(apply-reduction-relation reduction (term (return 0)))` | `#t`; τ = Int |
| `unbox (box ( #\, ⇒ (return 0)))` | `(judgment-holds (block-type () (unbox (box ( #\, ⇒ (return 0)))) σ none C))` | `(apply-reduction-relation reduction (term (unbox (box ( #\, ⇒ (return 0))))))` | `#t`; σ = `(#\, → Int)`|
| `def block = ( #\, ⇒ (return 0)) #\; return (box block)` | `(judgment-holds (statement-type () (def block = ( #\, ⇒ (return 0)) #\; (return (box block))) τ none C))` |

# Negative Unit Tests

* `box (unbox 0)`

## Typing

`(judgment-holds (expr-type () (box (unbox 0)) (σ at C)))
`
### Expected Output
`#f`
## Reduction

*TODO: Try returning a block which is not boxed*

*TODO: Try type checking block which does not have all of its capabilities*
