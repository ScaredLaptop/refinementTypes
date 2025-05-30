#lang racket
(require "predicates.rkt")
(require redex)
(define-extended-language TypedLambda/Inference Constraints
  [v variable-not-otherwise-mentioned] ; value variable
  [b ::= Int Bool]                    ; basic types
  [r ::= {HOLE x} {v : p}]            ; refinements
  [t s ::=                            ; types
      b                               ;   base types
      (b r)                           ;   refined base types  Int {v : ...}
      ((x : t) -> s)]                 ;   dependent function types
  [k ::= B ★]                         ; kinds (base or star)
  [Γ • (x : t Γ)]                     ; variable environment
  [addition-op ::= add sub mul div]   ; arithmetic primitives
  [bool-op     ::= equals gt lt leq geq] ; comparison primitives
  [refinement-op ::= addition-op bool-op]
  [constants ::= refinement-op integer bool]
  [e ::= constants                    ; expressions
         x                            ;   variables
         (let (x = e) in e)           ;   let‑binding
         (λ (x) e)                    ;   lambda
         (e x)                        ;   application
         (e : t)                      ;   type annotation
         (if x then e else e)         ;   conditional
         (rec x = (e : t) in e)       ;   recursive let
       ])   

(define hole-cache (make-hash))

(hash-set! hole-cache 'hole1 (term (<= 0 z)))

(define-metafunction TypedLambda/Inference
  sub-typed-lambda : e x e -> e
  [(sub-typed-lambda e_1 x_1 e_2) (substitute e_1 x_1 e_2)])

(define-metafunction TypedLambda/Inference
  sub-typed-lambda-type : t x x -> t
  [(sub-typed-lambda-type t_1 x_1 x_2) (substitute t_1 x_1 x_2)])

(define-metafunction TypedLambda/Inference
  extend : Γ x t -> Γ
  [(extend Γ x t) (x : t Γ)])

(define-metafunction TypedLambda/Inference
  lookup : Γ x -> t or #f
  [(lookup •            _ ) #f]
  [(lookup (x  : t Γ) x ) t]
  [(lookup (_  : _ Γ) y ) (lookup Γ y)])

(define-metafunction TypedLambda/Inference
  free? : Γ x -> #t or #f
  [(free? •            _ ) #t]
  [(free? (x  : t Γ) x ) #f]
  [(free? (_  : _ Γ) y ) (free? Γ y)])

(define-metafunction TypedLambda/Inference
  Length : Γ -> integer
  [(Length •) 0]
  [(Length (x : t Γ)) ,(+ 1 (term (Length Γ)))])

(define-metafunction TypedLambda/Inference
  GetFreshVar : Γ -> x
  [(GetFreshVar •) ,(string->symbol "t0")]
  [(GetFreshVar (x : t Γ)) ,(string->symbol (format "t~a" (+ 1 (term (Length Γ)))))] )

(define-judgment-form TypedLambda/Inference
  #:mode (wf-predicate I I)
  #:contract (wf-predicate Γ p)
  [------------- (wf-predicate Γ p)])

(define-judgment-form TypedLambda/Inference
  #:mode (wf-type I I O)
  #:contract (wf-type Γ t k)
  [(wf-predicate (extend Γ x b) p)
   ------------------------------------ "WF-Base"
   (wf-type Γ (b {x : p}) B)]
  [(wf-type Γ s k_1)
   (wf-type (extend Γ x s) t k_2)
   ------------------------------------ "WF-Fun"
   (wf-type Γ ((x : s) -> t) ★)])

(define-judgment-form TypedLambda/Inference
  #:mode (ent-type I I)
  #:contract (ent-type Γ c)
  [(side-condition (SmtValid c))
   ---------- "ENT-EMP"
   (ent-type • c)]
  [(ent-type Γ (forall (x b) (implies p c)))
   ----------- "ENT-EXT"
   (ent-type (x : (b {x : p}) Γ) c)])

(define-judgment-form TypedLambda/Inference
  #:mode (subtype-type I I I)
  #:contract (subtype-type Γ t t)
  [(ent-type Γ (forall (v_1 b) (implies p_1 (sub-constraints p_2 v_2 v_1))))
   ------------------------------------- "SUB-BASE"
   (subtype-type Γ (b {v_1 : p_1}) (b {v_2 : p_2}))]
  [-------------- (subtype-type Γ (b {v : p}) b)]
  [(subtype-type Γ s_2 s_1)
   (subtype-type (extend Γ x_2 s_2) (sub-typed-lambda-type t_1 x_1 x_2) t_2)
   ------- "SUB-FUN"
   (subtype-type Γ ((x_1 : s_1) -> t_1) ((x_2 : s_2) -> t_2))])


(define (get-op-refinement op)
  (case op
    [(add) '+]
    [(sub) '-]
    [(mul) '*]
    [(div) '/]
    [(equals) '=]
    [(gt)    '>]
    [(lt)    '<]
    [(leq)   '<=]
    [(geq)   '>=]
    [else (error "Unknown operator:" op)]))

(define arithmetic-ops '(add sub mul div))
(define comparison-ops '(equals gt lt leq geq))


(define (gen-racket-prim-op-expr refinement-op)
  (define op (get-op-refinement refinement-op))
  (match (map gensym '(x y v))
    [(list x y v)
     (begin (displayln (format "gen-op generated ~a" v)) (if (member refinement-op arithmetic-ops)
         `((,x : (Int {,x : true}))
           ->
           ((,y : (Int {,y : true}))
            ->
            (Int {,v : (= ,v (,op ,x ,y))})))
         `((,x : (Int {,x : true}))
           ->
           ((,y : (Int {,y : true}))
            ->
            (Bool {,v : (and (or (not ,v) (,op ,x ,y))
                (or ,v (not (,op ,x ,y))) )})))))]))

(define-metafunction TypedLambda/Inference
  prim : constants -> t
  [(prim refinement-op) ,(gen-racket-prim-op-expr (term refinement-op))]
  [(prim integer)  (Int {v : (= v integer)}) (where v ,(gensym 'v))]
  [(prim true)    (Bool {v : (= v true)}) (where v ,(gensym 'v))]
  [(prim false)   (Bool {v : (= v false)}) (where v ,(gensym 'v))] )

(define-metafunction TypedLambda/Inference
 self : x t -> t
 [(self x (b {v : p})) (b {v_new : (and p (= v_new x))})
    
    (where v_new ,(gensym "v"))
    (side-condition (displayln (format "self generated ~a" (term v_new))))
 ]
 [(self x t) t]
)

(define-judgment-form TypedLambda/Inference
  #:mode (synthesis-type I I O)
  #:contract (synthesis-type Γ e t)
  [(where constants_1 e_1)
   -------- "SYN-CON"
   (synthesis-type Γ e_1 (prim constants_1))]
  [(where t_found (lookup Γ x))
   (side-condition (not (equal? (term t_found) #f)))
   --------- "SYN-VAR"
   (synthesis-type Γ x (self x t_found))]
  [(hole-instantiation s t)
   (wf-type Γ t k)
   (check-type Γ e t)
   ----------------- "SYN-ANN"
   (synthesis-type Γ (e : s) t)]
  [(synthesis-type Γ e_1 ((x : s) -> t))
   (check-type Γ y s)
   ----------------- "SYN-APP"
   (synthesis-type Γ (e_1 y) (sub-typed-lambda-type t x y))])

(define-judgment-form TypedLambda/Inference
  #:mode (check-type I I I)
  #:contract (check-type Γ e t)
  [(synthesis-type Γ e_1 s)
   (subtype-type Γ s t)
   --------------------- "CHK-SYN"
   (check-type Γ e_1 t)]
  [(check-type (extend Γ x t_1) e_2 t_2)
   --------------------- "CHK-LAM"
   (check-type Γ (λ (x) e_2) ((x : t_1) -> t_2))]
  [(synthesis-type Γ e_1 t_1)
   (check-type (extend Γ x t_1) e_2 t_2)
   --------------------- "CHK-Let"
   (check-type Γ (let (x = e_1) in e_2) t_2)]
  [(where y (GetFreshVar Γ))
   (check-type Γ x Bool)
   (check-type (extend Γ y (Bool {y : (= x true)}))  e_1 t)
   (check-type (extend Γ y (Bool {y : (= x false)})) e_2 t)
   --------------------- "CHK-IF"
   (check-type Γ (if x then e_1 else e_2) t)]
  [(hole-instantiation s_1 t_1)
   (wf-type Γ t_1 k)
   (check-type (extend Γ x t_1) e_1 t_1)
   (check-type (extend Γ x t_1) e_2 t_2)
   --------------------- "CHK-REC"
   (check-type Γ (rec x = (e_1 : s_1) in e_2) t_2)])

(define-judgment-form
  TypedLambda/Inference
  #:mode (hole-instantiation I O)
  #:contract (hole-instantiation s t)
  [
    --------------- "INS-HOLE"
    (hole-instantiation (b {HOLE x}) (b{ : true }))
  ]
  [
    --------------- "INS-CONC"
    (hole-instantiation (b {v : p}) (b {v : true}))
  ]
  [
    (hole-instantiation s_1 s_2) (hole-instantiation t_1 t_2)
    --------------- "INS-FUN"
    (hole-instantiation ((x : s_1) -> t_1) ((x : s_2) -> t_2))
  ]
  )

(provide TypedLambda/Inference
         simplify-c sub-typed-lambda-type gen-racket-prim-op-expr
         wf-predicate sub-typed-lambda wf-type ent-type extend subtype-type
         prim synthesis-type free? check-type GetFreshVar lookup sub-constraints self)