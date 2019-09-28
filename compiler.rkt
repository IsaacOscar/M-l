#lang s-exp syntax/module-reader "runtime.rkt" #:read Read #:read-syntax Read-Syntax #:whole-body-readers? #t
(require racket brag/support)

; Top Level Compilation
; =====================================================================================================================================================
(define (Read in) (syntax->datum (Read-Syntax #f in)))
(define (Read-Syntax src port)
  (define ast (Desugar (Parse src (Lex port)))) ; Lex, parse and desugar
  `((Reduce ',ast))) ; return a racket module-body, that when evaluated, will perform the reduction

; Lexing
; =====================================================================================================================================================
(define Lexer (lexer-src-pos
   [(:or "def" "new" ";" ":=" "|" "," "=>" "=" "(" ")" "{" "}" "[" "]") ; these must be before the rule for identifiers
    (token lexeme lexeme)]
   [(:: alphabetic (:* alphabetic numeric "-")) ; identifiers
    (token 'IDENTIFIER lexeme)] ; note "Alphabetic" and "Numeric" are unicode properties
   [(:or whitespace (from/to "//" "\n") (from/to "/*" "*/")) ; whitespace/comments ; NOTE: does not support nested comments or // comments ending at eof
    (token 'WHITESPACE lexeme #:skip? #t)] ; Matches White_Space
   [(from/to "\"" "\"")
    (token 'STRING (trim-ends "\"" lexeme "\""))] ; remove the quotation marks from the string ; NOTE: does not support excape sequences
   [(:+ (:/ "0" "9"))
    (token 'NUMBER lexeme)]
   [(eof)
    (void)]))
(define (Lex port) 
  (port-count-lines! port) 
  (lambda () (Lexer port)))

; Parsing
; =====================================================================================================================================================
(require "grammar.rkt")
(define (Parse src lex) 
  ; brag ignores the "@" when processing the top-level rule (@expression), so it will return (expression e)
  ; where e is the AST for the expression, so I use cadr to return just the e
  (cadr (syntax->datum (parse src lex)))) ; strip syntax information, as redex dosn't support it?

; Desugaring
; =====================================================================================================================================================
(define Desugar
  (match-lambda
    [`(Id ,i); Redex only recognises "symbol"s as variable identifiers, whereas brag only produces strings
     (string->symbol i)]
    [`(Str ,s) ; A string literal is just an identity i such that "print(i)" prints the string
     ; $s dosn't need to be a fresh identifier as its scope is limited to this expression
     `[Let $s [New] [Seq [Def [print {[Eq $s]} {} [Seq [Print ,s] $s]]] $s]]]
    [`(Nat ,n)  ; succ( ... succ(zero)...), with n "succ"s
     (for/fold ([res 'zero]) ([_ (in-range (string->number n))]) `[Call succ ,res])]
    [`(List ,e ...) ; List e1 ... en = cons(e1, ... cons(en, empty)))
     (Desugar (for/fold ([res 'empty]) ([x e]) `[Call cons ,x ,res]))]
    [`(Lamb ,ps ,e) ; l := new; def apply(=l, ps...) { e }; l
     ; $l need not be fresh, because it can't clash with any identifier the user wrote in e
     ; and it will simply shadow any other $l's for any enclosing lambdas
     (Desugar `[Let $l [New] [Seq [Def [apply {[Eq $l] . ,ps} {} ,e]] $l]])]
    [`(,x ...) ; desuger all nested syntactic forms
     (map Desugar x)]
    [x  ; atomic form, leave unchanged
     x]))
