#lang racket
(require rackunit)
(require redex)
(require "../refinementInference-VC-synth.rkt")
(require "../refinementInference.rkt")


;∅ ⊢ 𝑥 : int → int{𝑦 :𝑦 = 𝑥 + 1} ≺: 𝑥 : int{0 ≤ 𝑥 } → int{𝜈 : 0 ≤ 𝜈 }
(test-equal?
    "sub-basic"
    (term 
        (sub-vc
            ((x : (Int {x : true})) -> (Int {y : (= y (+ x 1))}))
            ((x : (Int {x : (<= 0 x)})) -> (Int {v : (<= 0 v)}))
        )
    )
    (term (cand
  (forall (x Int) (implies (<= 0 x) true))
  (forall
   (x Int)
   (implies (<= 0 x) (forall (y Int) (implies (= y (+ x 1)) (<= 0 y)))))))
)

(test-equal? "synth-basic"
              (term (synth-vc (inc : ((x : (Int {v : (> x 0)})) -> (Int {v : (< x v)}))
                     (y : (Int {y : (> y 0)}) (y-1 : (Int {y-1 : (= y-1 (- y 1))}) •))) (inc y-1)))
              (term ((cand
   true
   (cand
    true
    (forall (y-1 Int) (implies (and (= y-1 (- y 1)) (= y-1 y-1)) (> y-1 0)))))
  (Int (v : (< y-1 v)))))
              )

(test-true "check-basic"
    (redex-match? 
        TypedLambda/Inference
        (cand (cand (cand true (cand true (forall (x Int) (implies (and (>= 0 x) (= x x)) true)))) (cand true (forall (one Int) (implies (and (= one 1) (= one one)) true)))) (forall (v Int) (implies (= v (+ x one)) (< x v))))
        (term (check-vc
            (x : (Int {x : (>= 0 x)}) 
                (one : (Int {one : (= one 1)}) •))
            ((add x) one)
            (Int {v : (< x v)})
        ))
    )
)

(test-true "check-basic 2"
    (redex-match? 
        TypedLambda/Inference
        (cand true (cand (cand (cand true (cand true (forall (x Int) (implies (and (<= 0 x) (= x x)) true)))) (cand true (forall (v Int) (implies (and (= v 1) (= v one)) true)))) (forall (v_1 Int) (implies (= v_1 (+ x one)) (< x v_1)))))
        (term (check-vc
            (x : (Int {x : (<= 0 x)}) •)
            (let (one = 1) in ((add x) one)) 
            (Int {v : (< x v)})
        ))
    )
)

(test-true "fresh test"
    (redex-match? 
        TypedLambda/Inference
        ((x : (Int (x : true))) -> (Int (v : (q y (v x)))))
    (term 
    (fresh-vc
        •
        ((x : (Int {x : true})) ->
            (Int {HOLE hole1})
        )
    )
    )
    )
)


(test-true "check-basic"
    (redex-match? 
        TypedLambda/Inference
        e
    (term (λ (x)
        (let (c = ((leq zero) x))      ; c = (0 ≤ x)
             in (if c
                    then x
                    else ((sub zero) x)))))
        ))
(test-true "check-basic"
    (redex-match? 
        TypedLambda/Inference
        e
    (term (rec zero = (0 : (Int {zero : (= zero 0)})) in 0))
        ))
(test-true "check-basic"
    (redex-match? 
        TypedLambda/Inference
        e
    (term 
        (rec assert = ((λ (x) 0) : 
    ((x : (Int {x : (not (= x 0))})) -> (Int {v2 : true})))
    in 
        (rec abs = ((λ (z)
        (let (c = ((leq zero) z))      ; c = (0 ≤ x)
             in (if c
                    then z
                    else ((sub zero) z)))) : ((z : (Int {z : true})) -> (Int {HOLE hole1}))) in 
                    (rec main = ((λ (y)
                            (let (l = (abs y)) in 
                                (let (o = ((leq zero) l)) in (assert o))
                            )
        
                        ) : 
                        ((y : (Int {y : true})) -> (Int {v : true}))) in main)
                    )
    ))  
    ))
(term 
(simplify-c
(check-vc
    (zero : (Int {zero : (= zero 0)})  •)
    (rec abs = ((λ (x)
        (let (c = ((leq zero) x))      ; c = (0 ≤ x)
             in (if c
                    then x
                    else ((sub zero) x)))) : ((x : (Int {x : true})) -> (Int {HOLE hole1}))) in abs)
    ((x : (Int {x : true})) -> (Int {HOLE hole1}))))
)

; (term 
; (simplify-c
; (check-vc
;     (zero : (Int {zero : (= zero 0)})  •)
;     (rec main = ((λ (y)
;         (let (q = (abs y)) in 
;             (let c = ((leq zero) q)
;                 (assert c)
;             )
;         )
    
;     ) : 
;     ((y : (Int {y : true})) -> (Int {v : true}))) in main)
;     ((y : (Int {y : true})) -> (Int {v1 : true}))
;     )))

(term 
(simplify-c
(check-vc
    •
    (rec zero = (0 : (Int {zero : (= zero 0)})) in (rec assert = ((λ (x) 0) : 
    ((x : (Bool {x : x})) -> (Int {v2 : true})))
    in 
        (rec abs = ((λ (z)
        (let (c = ((leq zero) z))      ; c = (0 ≤ x)
             in (if c
                    then z
                    else ((sub zero) z)))) : ((z : (Int {z : true})) -> (Int {HOLE hole1}))) in 
                    (rec main = ((λ (y)
                            (let (l = (abs y)) in 
                                (let (o = ((leq zero) l)) in (assert o))
                            )
                        
                        ) : 
                        ((y : (Int {y : true})) -> (Int {v : true}))) in main)
                    )
    ))

    ((x : (Int {x : true})) -> (Int {v1 : true}))
    )))

(term (fresh-vc • ((x : (Int {v2 : true})) -> (Int {HOLE hole2}))) )

; (term (simplify-c 
; (check-vc
;     (zero : (Int {zero : (= zero 0)})  •)
;     ((λ (x)
;         (let (c = ((leq zero) x))      ; c = (0 ≤ x)
;              in (if c
;                     then x
;                     else ((sub zero) x))))
    
;     ((x : (Int {x : true})) -> (Int {HOLE hole1}))
; )
; )))