#lang brag
; Note: the grammar has been carefully written so that it produces an AST (a list) as close as possible to the redex-grammar
; In particular:
;	all literal terminals are of the form /"foo", so they will not be included in the AST
;	names in all-upercase correspond to terminals produced by the lexer, and will be represented as a string-literal in the AST
;	non-terminals declared with an "@" will not wrap their body in a list
;	non-terminals declared with a "/" will wrap their body in a list
;	all other non-terminals are declared starting with a capital letter, they will wrap their body in a list, starting with the form-name as a symbol
; Thus the non-terminals starting with an upper case letter correspond to a PLT redex AST node.

@expression: Let | Seq | left-expression ; Top-level rule, a Mμl file must match this
@expression-list: [expression (/"," expression)*]
; A left-expression is anything that can appear on the LHS of a ";" without surrounding parantheses
@left-expression: New | Id | Def | Call | /"(" expression /")" | Lamb | Nat | Str | List

; Core expression forms
Let: Id /":=" left-expression /";" expression
Seq: left-expression /";" expression
Id: IDENTIFIER ; IDENTIFIER mathces a string, so this will be "desugared" into a symbol so that Redex can understand it
Call: Id /"(" expression-list /")"
New: /"new"

; Method definition forms
Def: /"def" method ; so that "method" matchs a single list
/method: Id /"(" paramater-list constraint-list /")" /"{" expression /"}"; paramater-list and constraint-list will each produce a single list
/paramater-list: [paramater (/"," paramater)*] ; Preceded with a "/" so that the paramaters are all wrapped in a list
@paramater: Id | Eq
Eq: /"=" Id
/constraint-list: ∅ | /"|" Cons (/"," Cons)* ; the "|" should only be present if there is at least one constraint
Cons: Id /"(" [Id (/"," Id)*] /")";

; Sugar forms
Nat: NUMBER ; sugar to succ( ... succ(zero) ...)
Str: STRING ; sugar for an identity $s such that print($s) prints STRING
Lamb: /"{" paramater-list /"=>" expression /"}"; sugar for an identity $l such that apply($l, values ...) = expression[paramaters := values ...]
List: /"[" expression-list /"]"; sugar for cons(e, ..., cons(e, empty))
