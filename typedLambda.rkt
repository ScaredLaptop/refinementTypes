#lang racket
(require "predicates.rkt")
(require redex)

(define-extended-language TypedLambda Constraints
  [v variable-not-otherwise-mentioned] ; value variable
  [b ::= Int] ; basic types
  [r ::= {v : p}] ; refinements i.e. {v: 0 < v}
  [t s ::= 
      b ;; I differ from the paper here and allow base types
      (b r)  ;; refined base type Int{({v : 0 < v})}
     ((x : t) -> s)]
  [k ::= B ★] ;;kinds (base or star)
  [Γ • (x : t Γ)] ;; variable binding
  [refinement-op ::= add sub mul div equals gt lt le ge]
  [constants ::= refinement-op integer]
  [e ::= constants ;;constants
     x ;; variables
     (let (x = e) in e) ;;  let
     (λ (x) e) ;; λ x.e
     (e x) ;; application
     (e : t) ;; type annotation
     ]
  #:binding-forms
  (λ (x) e #:refers-to x)
  (let (x = e) in e #:refers-to x)
  ((x : s) -> t #:refers-to x)
  (b {v : p} #:refers-to v)
  
  )

(define-metafunction TypedLambda
  sub-typed-lambda : e x e -> e
  [(sub-typed-lambda e_1 x_1 e_2) (substitute e_1 x_1 e_2)]
  )

(define-metafunction TypedLambda
  sub-typed-lambda-type : t x e -> t
  [(sub-typed-lambda-type t_1 x_1 e_1) (substitute t_1 x_1 e_1)]
  )

(define-metafunction TypedLambda
  extend : Γ x t -> Γ
  [(extend Γ x t) (x : t Γ)])


(define-metafunction TypedLambda
  lookup : Γ x -> t or #f
  [(lookup •            _ ) #f]
  [(lookup (x  : t Γ) x ) t]
  [(lookup (_  : _ Γ) y ) (lookup Γ y)])

(define-metafunction TypedLambda
  free? : Γ x -> #t or #f
  [(free? •            _ ) #t]
  [(free? (x  : t Γ) x ) #f]
  [(free? (_  : _ Γ) y ) (free? Γ y)])

;; I need to actually fix WF for predicates...
;; i.e. strip off the refinements and run
;; type deduction as normal
;; but for now....
;; Γ ⊢ p   (predicate p is well‑formed in Γ)
(define-judgment-form TypedLambda
  #:mode (wf-predicate I I)        ; Γ  p
  #:contract (wf-predicate Γ p)

  ;; TODO(liam): temporary stub: accept everything
  [ 
   -------------
   (wf-predicate Γ p)])

;; Well-formededness Judgements
(define-judgment-form
  TypedLambda
  #:mode (wf-type I I O) ;; Γ t -> k
  #:contract (wf-type Γ t k)
  ; Γ; 𝑥 :𝑏 ⊢ 𝑝
  ; -------------
  ; Γ ⊢ 𝑏 {𝑥 : 𝑝 } : 𝐵
  [
  (wf-predicate (extend Γ x b) p)
  ------------------------------------ "WF-Base"
  (wf-type Γ (b {x : p}) B)]
  
  ; ; Γ ⊢ 𝑠 : 𝑘𝑠     Γ; 𝑥 :𝑠 ⊢ 𝑡 : 𝑘𝑡   Wf-Fun 
  ; ; Γ ⊢ 𝑥 : 𝑠 → 𝑡 : ★
  [ (wf-type Γ s k_1) (wf-type (extend Γ x s) t k_2)
  ------------------------------------ "WF-Fun"
  (wf-type Γ ((x : s) -> t) ★)]


  ; Γ ⊢ 𝑡 : 𝐵 Wf-Kind Γ ⊢ 𝑡 : ★
  ; TODO(liam): something here infinite loops, I think it's
  ; based on how redex tries to solve this
  ; Add a counter here or rewrite to be bidirectional
   ; k ::= B ★
  ;  [
  ;   (wf-type Γ t B) (where k ★)
  ;  ------------------------------------- "WF-Kind"
  ;   (wf-type Γ t k)]
   )

;; Well-formededness Judgements
; (define-judgment-form
;   TypedLambda
;   #:mode (wf-type-counter I I O O) ;; Γ t -> k
;   #:contract (wf-type-counter Γ t int k)
;   ; Γ; 𝑥 :𝑏 ⊢ 𝑝
;   ; -------------
;   ; Γ ⊢ 𝑏 {𝑥 : 𝑝 } : 𝐵
;   [(wf-predicate (extend Γ x b) p)
;   ------------------------------------ "WF-Base"
;   (wf-type-counter Γ (b {x : p}) 10 B)]
  
;   ; Γ ⊢ 𝑠 : 𝑘𝑠     Γ; 𝑥 :𝑠 ⊢ 𝑡 : 𝑘𝑡   Wf-Fun 
;   ; Γ ⊢ 𝑥 : 𝑠 → 𝑡 : ★
;   [(wf-type-counter Γ s int_1 k_1) (wf-type-counter (extend Γ x s) t int_2 k_2)
;   ------------------------------------ "WF-Fun"
;   (wf-type-counter Γ ((x : s) -> t) int_1 ★)]


;   ; Γ ⊢ 𝑡 : 𝐵 Wf-Kind Γ ⊢ 𝑡 : ★
;   ; TODO(liam): something here infinite loops, I think it's
;   ; based on how redex tries to solve this
;   ; Add a counter here
;    ; k ::= B ★
;    [(where int) (wf-type-counter Γ t 10 B)
;    ------------------------------------- "WF-Kind"
;     (wf-type-counter Γ t int_1 ★)]
;    )

(define-judgment-form
  TypedLambda
  #:mode (ent-type I I) ;; Γ ⊢ 𝑐
  #:contract (ent-type Γ c)
  ; SmtValid(𝑐)
  ; ∅ ⊢𝑐
  [(side-condition (SmtValid c))
    ---------- "ENT-EMP"
    (ent-type • c)
  ]
  ; Γ ⊢ ∀𝑥 :𝑏. 𝑝 ⇒ 𝑐 
  ; ---------------- "ENT-EXT"
  ; Γ;𝑥:𝑏{𝑥:𝑝} ⊢𝑐
  [
    (ent-type Γ (forall (x b) (implies p c)))
    ----------- "ENT-EXT"
    (ent-type (x : (b {x : p}) Γ) c)
  ]
)

(define-judgment-form
  TypedLambda
  #:mode (subtype-type I I I) ;; Γ ⊢ 𝑡1 ≺: 𝑡2
  #:contract (subtype-type Γ t t)
  ; Γ⊢∀𝜈1:𝑏.𝑝1 ⇒𝑝2[𝜈2 :=𝜈1]
  ; Sub-Base
  ; Γ ⊢ 𝑏{𝜈1 :𝑝1} ≺: 𝑏{𝜈2 :𝑝2}
  [
   (ent-type Γ (forall (v_1 b) (implies p_1 (sub-constraints p_2 v_2 v_1))))
   ------------------------------------- "SUB-BASE"
   (subtype-type Γ (b {v_1 : p_1}) (b {v_2 : p_2}))
   ]
  
  ;; for convenience Int {v : p} :<  Int
  [
  --------------
  (subtype-type Γ (b {v : p}) b)
  ]

  ; Γ⊢𝑠2 ≺:𝑠1 Γ;𝑥2:𝑠2 ⊢𝑡1[𝑥1 :=𝑥2] ≺:𝑡2
  ; SUB-FUN
  ; Γ⊢𝑥1:𝑠1 →𝑡1 ≺:𝑥2:𝑠2 →𝑡2
  [
    (subtype-type Γ s_2 s_1) (subtype-type (extend Γ x_2 s_2) (sub-typed-lambda-type t_1 x_1 x_2) t_2)
    ------- "SUB-FUN"
    (subtype-type Γ ((x_1 : s_1) -> t_1) ((x_2 : s_2) -> t_2))
  ]
)

;; ops: + - * / = < > <= >=
;; 2 op primitives (add a b)
;;   a: int -> b : int ->  int {v : v = x + y}
(define (get-op-refinement op)
  (case op
    [(add) '+]
    [(sub) '-]
    [(mul) '*]
    [(div) '/]
    [(equals) '=]
    [(gt) '>]
    [(lt) '<]
    [(le) '<=]
    [(ge) '>=]
    [else (error "Unknown operator:" op)]))

(define (gen-racket-prim-op-expr refinement-op)
  (define op (get-op-refinement refinement-op))
  (match (map syntax->datum (generate-temporaries '(x y v)))
    [(list x y v)
     `((,x : (Int {,x : true}))
       ->
       ((,y : (Int {,y : true}))
        ->
        (Int {,v : (= ,v (,op ,x ,y))})))]))

(define-metafunction TypedLambda
  prim : constants -> t
  [(prim refinement-op) ((x : (Int {x : true})) -> ((y : (Int {y : true})) -> (Int {v : (= v (,(get-op-refinement (term refinement-op)) x y))} )))]
  [(prim integer) (Int {v : (= v integer)})]
)

(define-judgment-form
  TypedLambda
  #:mode (synthesis-type I I O) ; Γ⊢𝑒⇒𝑡
  #:contract (synthesis-type Γ e t)
  ; prim(c)=𝑡 
  ; Γ ⊢ c ⇒ 𝑡
  ;Syn-Con
  [
    (where constants_1 e_1)
    ---------- "SYN-CON"
    (synthesis-type Γ e_1 (prim constants_1))
  ]
  ; Γ(𝑥)=𝑡 
  ; SYN-VAR
  ; Γ ⊢ 𝑥 ⇒ 𝑡
  [
  (where t_found (lookup Γ x)) (side-condition (not (equal? (term t_found) #f)))
  --------- "SYN-VAR"
  (synthesis-type Γ x t_found)
  ]
  ; Γ⊢𝑡:𝑘    Γ⊢𝑒⇐𝑡 Γ 
  ; ------------- SYN-ANN
  ;⊢ 𝑒 :𝑡 ⇒ 𝑡
  [
    (wf-type Γ t k) (check-type Γ e t)
    --------------------- "SYN-ANN"
    (synthesis-type Γ (e : t) t)
  ]
  ; Γ⊢𝑒⇒𝑥:𝑠→𝑡 Γ⊢𝑦⇐𝑠
  ; ------------------ SYN-APP
  ; Γ ⊢ 𝑒 𝑦 ⇒ 𝑡 [𝑥 := 𝑦]
  [
    (synthesis-type Γ e_1 ((x : s) -> t)) (check-type Γ y s)
    --------------------- "SYN-APP"
    (synthesis-type Γ (e_1 y) (sub-typed-lambda-type t x y))
  ]
)
(define-judgment-form
  TypedLambda
  #:mode (check-type I I I) ; Γ⊢𝑒⇐𝑡
  #:contract (check-type Γ e t)
  ; Γ⊢𝑒⇒𝑠  Γ⊢𝑠≺:𝑡 
  ; ----------- "CHK-SYN"
  ; Γ⊢𝑒⇐𝑡
  [
    (synthesis-type Γ e_1 s) (subtype-type Γ s t)
    --------------------- "CHK-SYN"
    (check-type Γ e_1 t)
  ]
  ; Γ;𝑥:𝑡1 ⊢𝑒⇐𝑡2
  ; -------------- "CHK-LAM"
  ; Γ⊢𝜆𝑥.𝑒⇐𝑥:𝑡1 →𝑡2
  [
    (check-type (extend Γ x t_1) e_2 t_2)
    --------------------- "CHK-LAM"
    (check-type Γ (λ (x) e_2) ((x : t_1) -> t_2))
  ]
  ;Γ⊢𝑒1 ⇒𝑡1 Γ;𝑥:𝑡1 ⊢𝑒2 ⇐𝑡2
  ; ---------- Chk-Let
  ; Γ⊢let𝑥 =𝑒1 in𝑒2 ⇐𝑡2
  [
    (synthesis-type Γ e_1 t_1) (check-type (extend Γ x t_1) e_2 t_2)
    --------------------- "CHK-Let"
    (check-type Γ (let (x = e_1) in e_2) t_2)
  ]
  )
(provide TypedLambda wf-predicate sub-typed-lambda wf-type ent-type extend subtype-type prim synthesis-type free? check-type)