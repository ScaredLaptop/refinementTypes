#lang racket
(require "refinementInference.rkt")
(require redex)

(define-metafunction TypedLambda/Inference
    flatten-env : Γ x ... -> any
    [(flatten-env • x ...) ,(reverse (term (x ...)))]
    [(flatten-env (x : t Γ) y ...) (flatten-env Γ x y ...)]
)

(define-metafunction TypedLambda/Inference
    gen-fresh-template : Γ t -> t
    [(gen-fresh-template Γ (b {HOLE x})) 
        ,(let ([new_binder (gensym "v")]
                [new_horn_var (gensym (string-append "𝜅-" (symbol->string (term x))))])
                    (term (b {,new_binder : (𝜅 ,new_horn_var ,(append (list new_binder) (term (flatten-env Γ))))}))
                )
    ]
)

(define-metafunction TypedLambda/Inference
 fresh-vc : Γ t -> t
[(fresh-vc Γ (b {HOLE x})) (gen-fresh-template Γ (b {HOLE x}))]
[(fresh-vc Γ (b {v : p})) (b {v : p})]
[(fresh-vc Γ ((x : s) -> t)) ((x : (fresh Γ s)) -> (fresh (extend Γ x s) t))]
)

(define-metafunction TypedLambda/Inference
    get-implication-constraint : x t c -> c
    [(get-implication-constraint x t (b {v : p}))
        (forall (x b) (implies (sub-constraints p v x) c))]
    [(get-implication-constraint x t c)
        c]
)

(define-metafunction TypedLambda/Inference
 sub-vc : t t -> c
 ;sub(𝑏{𝜈1 :𝑝1}, 𝑏{𝜈2 :𝑝2}) = ∀𝜈1 :𝑏. 𝑝1 ⇒ 𝑝2[𝜈2 := 𝜈1]
 [(sub-vc (b {v1 : p1}) (b {v2 : p2}))
    (forall (v1 b) (implies p1 (sub-constraints p2 v2 v1)))]
    ;sub(𝑥1:𝑠1 →𝑡1, 𝑥2:𝑠2 →𝑡2) = 𝑐𝑖 ∧(𝑥2 ::𝑠2) ⇒𝑐𝑜
    ; where 𝑐𝑖 = sub(𝑠2, 𝑠1)
    ; 𝑐𝑜 = sub(𝑡1 [𝑥1 := 𝑥2], 𝑡2)
    [(sub-vc ((x_1 : s_1) -> t_1) ((x_2 : s_2) -> t_2))
        (cand (sub-vc s_2 s_1)
            (get-implication-constraint x_2 s_2 (sub-vc (sub-constraints t_1 x_1 x_2) t_2)))])

(define-metafunction TypedLambda/Inference
 synth-vc : Γ e -> (c t)
 [(synth-vc Γ x) (true (lookup Γ x))]
 [(synth-vc Γ constants) (true (prim constants))]
 [(synth-vc Γ (e y)) ((cand
                       ,(first (term (synth-vc Γ e)))
                       (check-vc Γ y s)
                       )
                       (sub-typed-lambda-type t x y))]
 [(synth-vc Γ (e : t)) ((check-vc Γ e t) t)]
)

(define-metafunction TypedLambda/Inference
 check-vc : Γ e t -> c
 [(check-vc Γ (λ (x) e) ((x : t) -> s)) (get-implication-constraint x s (check-vc (extend Γ x s) e t))]
 [(check-vc Γ (let (x = e_1) in e_2) t_2) 
            (cand () ;;todo
                  (check-vc (extend Γ x t_1) e_2 t_2))
 ]
)


(provide gen-fresh-template fresh-vc flatten-env)