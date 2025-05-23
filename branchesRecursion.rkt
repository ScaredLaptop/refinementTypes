#lang racket
(require "predicates.rkt")
(require redex)

(define-extended-language TypedLambda/Recursion Constraints
  [v variable-not-otherwise-mentioned] ; value variable
  [b ::= Int Bool] ; basic types
  [r ::= {v : p}] ; refinements i.e. {v: 0 < v}
  [t s ::= 
      b ;; I differ from the paper here and allow base types
      (b r)  ;; refined base type Int{({v : 0 < v})}
     ((x : t) -> s)]
  [k ::= B ★] ;;kinds (base or star)
  [Γ • (x : t Γ)] ;; variable binding
  [refinement-op ::= add sub mul div equals gt lt leq geq]
  [constants ::= refinement-op integer bool]
  [e ::= constants ;;constants
     x ;; variables
     (let (x = e) in e) ;;  let
     (λ (x) e) ;; λ x.e
     (e x) ;; application
     (e : t) ;; type annotation
     (if x then e else e) ;; if-then-else
     (rec x = (e : t) in e) ;; recursive let
     ]
  ; #:binding-forms
  ; (λ (x) e #:refers-to x)
  ; (let (x = e) in e #:refers-to x)
  ; ((x : t) -> s #:refers-to x)
  ; (v : b {v : p} #:refers-to v)
  ; (x : t Γ #:refers-to x)
)   

(define-metafunction TypedLambda/Recursion
  sub-typed-lambda : e x e -> e
  [(sub-typed-lambda e_1 x_1 e_2) (substitute e_1 x_1 e_2)]
  )

(define-metafunction TypedLambda/Recursion
  sub-typed-lambda-type : t x x -> t
  [(sub-typed-lambda-type t_1 x_1 x_2) (substitute t_1 x_1 x_2)]
  )

(define-metafunction TypedLambda/Recursion
  extend : Γ x t -> Γ
  [(extend Γ x t) (x : t Γ)])


(define-metafunction TypedLambda/Recursion
  lookup : Γ x -> t or #f
  [(lookup •            _ ) #f]
  [(lookup (x  : t Γ) x ) t]
  [(lookup (_  : _ Γ) y ) (lookup Γ y)])

(define-metafunction TypedLambda/Recursion
  free? : Γ x -> #t or #f
  [(free? •            _ ) #t]
  [(free? (x  : t Γ) x ) #f]
  [(free? (_  : _ Γ) y ) (free? Γ y)])

(define-metafunction TypedLambda/Recursion
  Length : Γ -> integer
  [(Length •) 0]
  [(Length (x : t Γ)) ,(+ 1 (term (Length Γ)))])

(define-metafunction TypedLambda/Recursion
  GetFreshVar : Γ -> x
  [(GetFreshVar •) ,(string->symbol "t0")]
  [(GetFreshVar (x : t Γ)) ,(string->symbol (format "t~a" (+ 1 (term (Length Γ)))))])

(define-judgment-form TypedLambda/Recursion
  #:mode (wf-predicate I I)        ; Γ  p
  #:contract (wf-predicate Γ p)

  [ 
   -------------
   (wf-predicate Γ p)])

;; Well-formededness Judgements
(define-judgment-form
  TypedLambda/Recursion
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
;   TypedLambda/Recursion
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
  TypedLambda/Recursion
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
  TypedLambda/Recursion
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
    [(leq) '<=]
    [(geq) '>=]
    [else (error "Unknown operator:" op)]))

(define (gen-racket-prim-op-expr refinement-op)
  (define op (get-op-refinement refinement-op))
  (match (map gensym '(x y v))
    [(list x y v)
     `((,x : (Int {,x : true}))
       ->
       ((,y : (Int {,y : true}))
        ->
        (Int {,v : (= ,v (,op ,x ,y))})))]))

(define-metafunction TypedLambda/Recursion
  prim : constants -> t
  [(prim refinement-op) ,(gen-racket-prim-op-expr (term refinement-op))]
  [(prim integer) (Int {v : (= v integer)})]
  [(prim true) (Bool {v : true})]
  [(prim false) (Bool {v : (not v)})]
)

(define-metafunction TypedLambda/Recursion
  self : x t -> t
  [(self x (b {v : p})) (b {v : (and p (= v x))})] 
  [(self x t) t]
)

(define-judgment-form
  TypedLambda/Recursion
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
  (synthesis-type Γ x (self x t_found))
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
  TypedLambda/Recursion
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
  ; 𝑦 is fresh Γ⊢𝑥 ⇐bool
  ; Γ;𝑦:{int:𝑥} ⊢ 𝑒1 ⇐ 𝑡 Γ;𝑦:{int:¬𝑥} ⊢ 𝑒2 ⇐ 𝑡
  ; ------------- CHK-IF
  ; Γ⊢if 𝑥 then 𝑒1 else 𝑒2 ⇐𝑡
  [
    (where y (GetFreshVar Γ)) (check-type Γ x Bool)
    (check-type (extend Γ y (Int {y : (= x true)})) e_1 t) 
    (check-type (extend Γ y (Int {y : (= x false)})) e_2 t)
    --------------------- "CHK-IF"
    (check-type Γ (if x then e_1 else e_2) t)
  ]
  ; Γ⊢𝑡1 :𝑘 Γ;𝑥:𝑡1 ⊢𝑒1 ⇐𝑡1 Γ;𝑥:𝑡1 ⊢𝑒2 ⇐𝑡2
  ; ----------------- CHK-REC
  ; Γ ⊢ rec 𝑥 = 𝑒1 :𝑡1 in 𝑒2 ⇐ 𝑡2
  [
    (wf-type Γ t_1 k) (check-type (extend Γ x t_1) e_1 t_1) (check-type (extend Γ x t_1) e_2 t_2)
    --------------------- "CHK-REC"
    (check-type Γ (rec x = (e_1 : t_1) in e_2) t_2)
  ]
  )
(provide TypedLambda/Recursion sub-typed-lambda-type gen-racket-prim-op-expr wf-predicate sub-typed-lambda wf-type ent-type extend subtype-type prim synthesis-type free? check-type GetFreshVar)

(redex-match? TypedLambda/Recursion c
                  (term (Int (x : (and (> x 0) (= x x))))))
