#lang racket
(require rackunit)
(require redex)
(require "../typedLambda.rkt")

(test-true "Basic types"
           (redex-match? TypedLambda b (term Int)))
(test-false "Basic types"
            (redex-match? TypedLambda b (term Bool)))

(test-true "constants"
           (redex-match? TypedLambda constants (term 1)))
(test-true "constants"
           (redex-match? TypedLambda constants (term mul)))

(test-true "refinements"
           (redex-match? TypedLambda r (term {v : (and 0 x)})))

(test-true "types"
           (redex-match? TypedLambda t (term (Int {v : (< 0 v)}))))

(test-true "typed var"
           (redex-match? TypedLambda (x : t) (term (x : (Int {v : (< 0 v)}))))
           )
(test-true "fxn type"
           (redex-match? TypedLambda t (term ((a : (Int {v : (< 0 a)})) -> (Int {v : (< 0 a)}))))
           )

(test-true "nested fxn type"
           (redex-match? TypedLambda t (term ((a : (Int {v : (< 0 a)})) -> ((a : (Int {v : (< 0 a)})) -> (Int {v : (< 0 a)})))))
           )

(define (≈? a b) (alpha-equivalent? TypedLambda a b))

;; b{v : p}[v := z] = b{v:p}
(test-true "substitution 1" (≈?
                             (term (sub-typed-lambda (a : (Int {v : (< 0 v)})) v b))
                             (term (a : (Int {v : (< 0 v)}))
                                   )))
;; 𝑏{𝜈:𝑝}[𝑦 :=𝑧] = 𝑏{𝜈:𝑝[𝑦 :=𝑧]}
(test-true "substitution 2" (≈?
                             (term (sub-typed-lambda (a : (Int {v : (< 0 c)})) c b))
                             (term (a : (Int {v : (< 0 b)}))
                                   )))
;; (𝑥 :𝑠 → 𝑡)[𝑥 := 𝑧] = 𝑥 :𝑠[𝑥 := 𝑧] → 𝑡
(test-true "substitution 3" (≈?
                             (term (sub-typed-lambda (c : ((a : (Int {v : (< 0 a)})) -> (Int {v : (< 0 a)}))) a b))
                             (term (c : ((a : (Int {v : (< 0 b)})) -> (Int {v : (< 0 a)}))))
                             ))

;; (𝑥 :𝑠 → 𝑡)[𝑦 := 𝑧] = 𝑥 :𝑠[𝑦 := 𝑧] → 𝑡[𝑦 := 𝑧]
(test-true "substitution 4" (≈?
                             (term (sub-typed-lambda (c : ((d : (Int {v : (< 0 a)})) -> (Int {v : (< 0 a)}))) a b))
                             (term (c : ((d : (Int {v : (< 0 b)})) -> (Int {v : (< 0 b)}))))
                             ))

;; 
(test-true
 "WF predicate"
 (judgment-holds
  (wf-predicate • (and x y))))
(test-true
 "WF predicate"
 (judgment-holds
  (wf-predicate (x : (Int {v : true}) •) (and x y))))


(test-true
 "WF-Base -empty ctx"
 (judgment-holds
  (wf-type • 
           (Int {v : (< 0 a)})
           k)))
; TODO(liam): something here infinite loops, I think it's
; based on how redex tries to solve this
; (test-true
;  "WF-Kind lifts to ★"
;  (judgment-holds
;   (wf-type •
;            (Int {v : (< 0 a)})
;            ★)))

(test-true
"WF-Fun"
 (judgment-holds
  (wf-type •
           ((a : (Int {v : (< 0 a)})) -> (Int {v : (< 0 a)}))
           ★)))

(test-false
"WF-Fun"
 (judgment-holds
  (wf-type •
           ((a : (Int {v : (< 0 a)})) -> (Int {v : (< 0 a)}))
           B)))

(test-true
"ENT-EMP"
  (judgment-holds
    (ent-type •
             (and true true))))

(test-false
"ENT-EMP"
  (judgment-holds
    (ent-type •
             (and true false))))

(test-true "Typing 1"
           (redex-match? TypedLambda Γ (term (x : Int •)))
           )
(test-equal? "Typing 2"
           (term (extend • x Int))
           (term (x : Int •))
           )

(test-true "Broken 1"
           (redex-match? TypedLambda c (term (forall (x Int) (implies (and x y) (and y x)))))
           )
(test-true "Broken 2"
           (redex-match? TypedLambda (b (x : p)) (term (Int {x : (< 0 x)})))
           )
(test-true "Broken 3"
           (redex-match? TypedLambda (x (b (v : p))) (term (x (Int {x : (< 0 x)}))))
           )
(test-true "Broken 4"
           (redex-match? TypedLambda (Γ x (b (v : p))) (term (• x (Int {x : (< 0 x)}))))
           )
           
(test-true
"ENT-EXT"
 (judgment-holds
    (ent-type
     (extend (extend • x (Int (x : (< x 0)))) y (Int (y : (= y (+ x 1)))) )
     (<= y 0) 
    )
 )
)

; ;; todo(liam): expand testing, especially making
; ;; sure these derivations are correct

(test-true 
"SUB-BASE"
  (judgment-holds
    (subtype-type
     (extend • x (Int {x : (< 0 x)}))
     (Int {y : (= y (+ x 1))})
     (Int {v : (<= 0 v)})
    )
  )
)

(test-true
  "convenience"
  (judgment-holds
    (subtype-type
     •
     (Int {x : (<= 0 x)})
     Int
    )
  )
)
(test-true 
"SUB-FUN"
(judgment-holds
  (subtype-type
    •
    ((x : (Int {x : true})) -> (Int {v : (= v (+ x 1))}))
    ((x : (Int (x : (<= 0 x)))) -> (Int {y : (<= 0 y)}))
  )))

(test-true "l" (redex-match? TypedLambda
  t (term ((x1 : Int)
    ->                        
    (Int {y : (= y (+ x1 1))})))))

(test-true "l" (redex-match? TypedLambda
  t (term ((z : (Int {z : (< 0 z)}))
    ->                   
    (Int {v : (< 0 v)})))))

; (test-true
; "SUB-BASE simple"
;  (judgment-holds
;   (subtype-type
;    •
   
    
; )))


(test-true
 "SUB-FUN-rename"
 (judgment-holds
  (subtype-type
   •
   ((x : (Int {x : true}))
    ->                        
    (Int {y : (= y (+ x 1))}))
   ((z : (Int {z : (< 0 z)}))
    ->                   
    (Int {v : (< 0 v)})))))

; ; todo(liam) fix this failling case
; (test-true 
; "SUB-FUN"
; (judgment-holds
;   (subtype-type
;     •
;     ((x : Int) -> (Int {y : (= y (+ x 1))}))
;     ((z : (Int {z : (<= 0 z)})) -> (Int {v : (<= 0 v)})))
;   )
; )

; (show-derivations
; (build-derivations (subtype-type
;     •
;     ((x : (Int (x : true))) -> (Int {y : (= y (+ x 1))}))
;     ((z : (Int {z : (<= 0 z)})) -> (Int {v : (<= 0 v)})))
;   )
; )

(test-true "prim test 1" (≈?
                             (term (prim 3))
                             (term (Int {v : (= v 3)}))
                                   ))
(test-true "prim test 2" (≈?
                             (term (prim add))
                             (term ((a : (Int {a : true})) -> ((b : (Int {b : true})) -> (Int (c : (= c (+ a b)))))))
                                   ))

(test-true
 "SYN-CON INT"
  (judgment-holds
  (synthesis-type
    •
    3
    (Int {v : (= v 3)})
  )
  )
)

(test-true 
  "basic"
(redex-match? TypedLambda
  constants
  (term mul)
))

(test-true
 "SYN-CON MUL"
 (judgment-holds (synthesis-type • mul _)))
;; todo(liam): there's some funky business going on here
(test-true
  "SYN-CON MUL"
 (judgment-holds
   (synthesis-type
     •
     mul
     ((x : (Int (any_1 : true))) -> ((y : (Int {any_2 : true})) -> (Int (z : (= z (* x y))))))
     ))) 

(test-true
  "SYN-VAR"
 (judgment-holds
   (synthesis-type
     (x : Int •)
     x
     Int
     )))

(test-equal?
"free"
 (term (free? •
     x))
    #t
)

(test-equal?
"free"
 (term (free? (t : (Int {t : true}) •)
     t))
    #f
)

(test-false
  "SYN-VAR"
 (judgment-holds
   (synthesis-type
    •
     x
     Int
     )))
  
(test-true
  "WF-KIND 2"
  (judgment-holds
    (wf-type
      (t : (Int {t : true}) •)
      (Int {v : true})
      B
    )
  )
)

(test-true
  "SYN-ANN"
 (judgment-holds
   (synthesis-type
     (t : (Int {t : true}) •)
     (t : (Int {t : true}))
     (Int {v : true})
     )))

; (show-derivations
; (build-derivations
;  (synthesis-type
;    (a : (Int {a : true}) •)
;    (a : (Int {a : true}))
;    (Int {a : true})
;  )))

(test-true
"CHK-SYN"
  (judgment-holds
    (check-type
      (a : (Int {a : (> a 0)}) •)
      (a : (Int {a : (> a 0)}))
      (Int {a : (> a 0)})
      )))

(test-true
"SYN-APP"
  (judgment-holds
    (synthesis-type
      (x : (Int {x : (< 0 x)}) (y : (Int {y : (= y 1)}) •))
      ((add x) y)
      (Int {v : (= v (+ x y))})
      ))
)
