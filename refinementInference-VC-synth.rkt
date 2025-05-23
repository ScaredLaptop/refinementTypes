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
                [new_horn_var (gensym (string-append "q-" (symbol->string (term x))))])
                    (term (b {,new_binder : (q ,new_horn_var ,(append (list new_binder) (term (flatten-env Γ))))}))
                )
    ]
)

(define-metafunction TypedLambda/Inference
 fresh-vc : Γ t -> t
[(fresh-vc Γ (b {HOLE x})) (gen-fresh-template Γ (b {HOLE x}))]
[(fresh-vc Γ (b {v : p})) (b {v : p})]
[(fresh-vc Γ ((x : s) -> t))
    ((x : s_prime) -> t_prime)
    (where s_prime (fresh-vc Γ s))
    (where t_prime (fresh-vc (extend Γ x s) t))
]
)

(define-metafunction TypedLambda/Inference
    get-implication-constraint : x t c -> c
    [(get-implication-constraint x (b {x : p}) c)
        (forall (x b) (implies (sub-constraints p v x) c))]
    [(get-implication-constraint x t c)
        c]
)

(define-metafunction TypedLambda/Inference
 sub-vc : t t -> c
 [(sub-vc (b {v_1 : p_1}) (b {v_2 : p_2}))
    (forall (v_1 b) (implies p_1 (sub-constraints p_2 v_2 v_1)))]
[(sub-vc ((x_1 : s_1) -> t_1) ((x_2 : s_2) -> t_2))
        (cand (sub-vc s_2 s_1)
            (get-implication-constraint x_2 s_2 (sub-vc (sub-typed-lambda-type t_1 x_1 x_2) t_2)))])           

(define-metafunction TypedLambda/Inference
 self-vc : x t -> t
 [(self-vc x (b {v : p})) (b {v : (and p (= v x))})]
 [(self-vc x t) t]
)

(define-metafunction TypedLambda/Inference
 synth-vc : Γ e -> (c t)
 [(synth-vc Γ x) (true (self-vc x t_x))
    (where t_x (lookup Γ x))
 ]
 [(synth-vc Γ constants_1) (true (prim constants_1))]
 [(synth-vc Γ (e y))
   ((cand c_1 c_2) (sub-typed-lambda-type t_1 x_1 y))
   (where (c_1 ((x_1 : s_1) -> t_1)) (synth-vc Γ e))
   (where c_2 (check-vc Γ y s_1))
  ]
 [(synth-vc Γ (e : s))
 (c t)
 (where c (check-vc Γ e t))
 (where t (fresh-vc Γ s))
 ])

(define-metafunction TypedLambda/Inference
 check-vc : Γ e t -> c
 [(check-vc Γ (λ (x) e) ((x : s) -> t)) (get-implication-constraint x s (check-vc (extend Γ x s) e t))]
 [(check-vc Γ (let (x = e_1) in e_2) t_2) 
    (cand 
        c_1
        (get-implication-constraint x t_1 c_2)
    )
    (where (c_1 t_1) (synth-vc Γ e_1))
    (where c_2 (check-vc (extend Γ x t_1) e_2 t_2))
 ]
 [(check-vc Γ (if x then e_1 else e_2) t)
  (cand c_1 c_2)
 (where c_1 (get-implication-constraint y (Bool {y : x}) (check-vc Γ e_1 t)))
 (where c_2 (get-implication-constraint y (Bool {y : (not x)}) (check-vc Γ e_2 t)))
 (where y ,(gensym 'y))
 ]
 [(check-vc Γ (rec x = (e_1 : s_1) in e_2) t)
  (cand c_1 c_2)
  (where c_1 (check-vc Γ_1 e_1 t)) 
  (where c_2 (check-vc Γ_1 e_2 t))
  (where Γ_1 (extend Γ x t_1))
  (where t_1 (fresh-vc Γ s_1))
 ]
 [(check-vc Γ e t)
   (cand c c_prime)
   (where (c s) (synth-vc Γ e))
   (where c_prime (sub-vc s t))
   ]
)

(provide gen-fresh-template simplify-c fresh-vc flatten-env sub-vc synth-vc check-vc self-vc)