#lang racket
(require redex/reduction-semantics)
(provide Reduce (all-from-out racket))

; Top level reduction function, with some very primitive error reporting
; ====================================================================================================================================================
(define (Reduce ast)
  (when (not (redex-match? Language e ast))
     (println ast)
     (error "Bad Ast!"))
  (define res (apply-reduction-relation* Red (term [[] ,ast])))
  (when (not (redex-match? Language ([Ms g]) res))
    (redex-let Language ([[[Ms (in-hole ℰ r)]] res])
        (for-each println (list (term Ms) (term ℰ) (term r))))
    (term (Print-Redex ,res))
    (error "got stuck!")))

; Utility functions to generate fresh numbers
; =====================================================================================================================================================

(define Last-Fresh 0)
(define (Fresh-Number)
  (set! Last-Fresh (add1 Last-Fresh))
  Last-Fresh)

(caching-enabled? #f) ; turn of redex's caching, because I use (Fresh-Number) which is non-deterministic

; Grammar
; =====================================================================================================================================================

(define-language Language
  (e ::= t [New] [Def M] [Call μ e ...] [Seq e e] [Let x e e] [Print string]) ; t | new | def M | μ(e1, …, en | e; e' | x ≔ e; e' | Print s
  (t ::= x ι ) ; x | ι 
  (M ::= [μ {p ...} {c ...} e]) ; μ(p1, …, pn | c1, …, ck) { e }
  (p ::= t [Eq t]) ; t | =t
  (c ::= [Cons μ t ...]) ; μ(t1, …, tn)

  (ι ::= [@ natural]) ; @n, where n is an ID number
  (μ x ::= variable) ; identifiers
  (Ms ::= [M ...]) ; shorthand for M1, …, Mn
  (ℰ ::= hole [Call μ ι ... ℰ e ...] [Seq ℰ e] [Let x ℰ e]) ; □ | μ(ι1, …, ιn, ℰ, e1, …, ek) | ℰ; e | x ≔ ℰ; e

  (g  ::= t [Def M] [Print string]) ; an irreducable expression, only used for error reporting
  (r ::= [New] [Call μ g ...] [Seq g e] [Let x g e]) ; a redex, only used for error reporting

  #:binding-forms ; declares how variable scopes work
  [Let x e_1 e_2 #:refers-to x] ; i.e. x is in scope in e_2, but not e_1

  ; i.e. each p (which is of form "x") is in scope in p ..., c ..., and e
  ; (also, declarations in "p" shadow former declarations, redex dosn't have an option to make this an error as one would normally want
  ; e.g. [Def [foo {x x} {} x]] is perfectly valid, which for some reason, returns the first argument not the second)
  [Def [μ {p ...} {c ...} e] #:refers-to (shadow p ...)])


(default-language Language)

; Reduction rules
; =====================================================================================================================================================

; I need to split this up into to relations, since the usual rule (Ms1|ℰ[e1] → Ms2|ℰ[e2]  where Ms1|e1 → Ms2|e2) causes redex to run out of memory
(define-judgment-form Language #:mode (Red I O) #:contract (Red [Ms e] [Ms e]) ; Define Ms|e ⇒ Ms|e
  [(Red [Ms_1 (in-hole ℰ e_1)] [Ms_2 (in-hole ℰ e_2)]) ; Ms1|ℰ[e1] ⇒ Ms2|ℰ[e2]
   (SRed [Ms_1 e_1] [Ms_2 e_2])]) ; where Ms1|e1 → Ms2|e2

; Note: for redex's to recognise Red as a reduction relation, Red must take a single input and output (which just happen to be pairs)
(define-judgment-form Language #:mode (SRed I O) #:contract (SRed [Ms e] [Ms e]) ; Define Ms|e → Ms|e
  [(SRed [Ms [Seq ι e]] [Ms e])] ; Ms|ι; e → Ms|e
  [(SRed [Ms [Let x ι e]] [Ms (mf-apply Subs e [x := ι])])] ; Ms|x ≔ ι; e → Ms|e[x ≔ ι]
  [(SRed [Ms [New]] [Ms [@ ,(Fresh-Number)]])] ; Ms|new → Ms|ι, for fresh ι
  [(SRed [[M ...] [Seq [Def M_1] e]] [[M_1 M ...] e])] ; Ms|M; e → M, Ms|e
  
  [(SRed [Ms [Call μ ι ...]] [Ms e]); Ms|μ(ι1,  …, ιn) → Ms|e
   (where [M_1 ... M_2 M_3 ...] Ms) ; where Ms = M1, …, Mk, M', M"1, …, M"m
   (Applies Ms M_2 [Call μ ι ...] e); where Ms ⊢ M' ~ μ(ι1,  …, ιn) → e
   ; Redex only supports (foo args) ... as a condition inside judgement forms and when foo is also a judgement form
   ; In particular, this means I can't inline the body of NApplies
   (NApplies Ms M_1 [Call μ ι ...]) ...] ; Ms ⊢ M1 ≁ μ(ι1,  …, ιn), …, Ms ⊢ Mk ≁ μ(ι1,  …, ιn)

  [(SRed [Ms [Seq [Print string] e]] [Ms e]) ; Ms|print(s); e → Ms|e
   (side-condition ,(displayln (term string)))]) ; print to terminal

; Auxilary judgments
; =====================================================================================================================================================
(define-judgment-form Language #:mode (Applies I I I O) #:contract (Applies Ms M [Call μ ι ...] e) ; Define Ms ⊢ M ~ μ(ι1,  …, ιn) → e
  ; (Ms ⊢ def μ(p1, …, pn | c1, …, ck) {e} ~ μ(ι1, …, in))  → e[p1 := ι1, …, pn := ιn], where:
  [(Applies Ms [μ {p ..._1} {c ..._2} e] [Call μ ι ..._1] (mf-apply Subs e [p := ι] ...))
   (Par (mf-apply Subs p [p := ι] ...) ι) ... ; p1[p1 := ι1, …, pn := ιn] ~ ι1 and … and pn[p1 := ι1, …, pn := ιn] ~ ιn
   (Sat Ms (mf-apply Subs c [p := ι] ...)) ...]) ; Ms ⊢ c1[p1 := ι1, …, pn := ιn] and … and Ms ⊢ ck[p1 := ι1, …, pn := ιn]
   
(define-relation Language NApplies ⊆ Ms × M × [Call μ ι ...] ; Define Ms ⊢ M ≁ μ(ι1,  …, ιn)
  [(NApplies Ms M [Call μ ι ...]) ; Ms ⊢ M ≁ μ(ι1,  …, ιn), 
   (side-condition (not (judgment-holds (Applies Ms M [Call μ ι ...] e))))]) ; where ∄e ∙ Ms ⊢ M ~ μ(ι1,  …, ιn) → e

(define-relation Language Par ⊆ p × ι ; Define p ~ ι
  [(Par ι ι)] ; ι ~ ι holds
  [(Par [Eq ι] ι)]) ; =ι ~ ι holds

(define-relation Language Sat ⊆ Ms × c ; Define Ms ⊢ μ(ι1,  …, ιn) 
  [(Sat [Ms] [Cons μ ι ...]) ;  Ms ⊢ μ(ι1,  …, ιn) 
   (Applies Ms M_2 [Call μ ι ...] e) ; where ∃e ∙ Ms|M' ~ μ(ι1,  …, ιn) → e
   (where [M_1 ... M_2 M_3 ...] Ms)]) ; Ms = M1, …, Mk, M', M"1, …, M"m
  
(define-metafunction Language Subs : any [p := ι] ... -> any ; Define X[p1 := ι1, …, pn := ιn] = X', for any metavariable X
  [(Subs any) ; X[] = X
   any]
  [(Subs any [[Eq t] := ι_0] [p_1 := ι_1] ...) ; X[=t ≔ ι0, p1 := ι1, …, pn := ιn] = X[p1 := ι1, …, pn := ιn]
   (Subs any [p_1 := ι_1] ...)]
  [(Subs any [x := ι_0] [p_1 := ι_1] ...) ; X[x ≔ ι0, p1 := ι1, …, pn := ιn] = X[x ≔ ι0][p1 := ι1, …, pn := ιn]
   ; where X[x ≔ ι0] is standard capture avoiding substitution
   (Subs (mf-apply substitute any x ι_0) [p_1 := ι_1] ...)])

; ====================================================================================================================================================
