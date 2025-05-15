#lang racket
(require "typedLambda.rkt")
(require redex)
(require rackunit)

(define-extended-language TypedLambda/ANF TypedLambda
  [val ::= x                       ; variables
          constants               ; ints, mul, …
          (λ (x) e_anf)]          ; lambdas are values too
  [eAnf ::=                      ; fully ANF expressions
           val
           (let ([x val]) eAnf)  ; *binding* form only allows val on RHS
           (eAnf x)])

(define-metafunction TypedLambda
  [(fresh-var Γ) ,(string->symbol
                   (format "t~a" (length (term Γ))))])

(define-metafunction TypedLambda/ANF
  ;; (anf e Γ)  → (values e_anf Γ')   ; Γ' = list of freshly bound vars
  [(anf x Γ)         (values x Γ)]
  [(anf constants Γ) (values constants Γ)]
  [(anf (λ (x) e) Γ)
   (let-values ([(body Γ1) (anf e Γ)])
     (values (λ (x) body) Γ1))]

  ;; let – convert binding and body
  [(anf (let ([x e1]) e2) Γ)
   (let-values ([(e1* Γ1) (anf e1 Γ)])
     (let-values ([(e2* Γ2) (anf e2 Γ1)])
       (values (let ([x e1*]) e2*) Γ2)))]

  ;; application – ensure func and arg are ANF and arg is a var
  [(anf (e1 e2) Γ)
   (let-values ([(f*  Γ1) (anf e1 Γ)])
     (let-values ([(a*  Γ2) (anf e2 Γ1)])
       (if (term (val? a*))
           (values (f* a*) Γ2)                   ; already variable
           (let ([w (fresh-var Γ2)])
             (values (let ([w a*]) (f* w))
                     (cons w Γ2))))))]
  ;; fall‑through (shouldn’t happen)
  [(anf e) ,(first (term (anf e •)))])


(check-equal?
   (term (anf (add1 (3 + 2))))
   (term
     (let ([t0 (+ 3 2)])
       (add1 t0))))

  (check-true
   (redex-match? TypedLambda/ANF eAnf
                 (term (anf (inc (if (> n 0) n 1))))))