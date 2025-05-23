#lang racket
(require rackunit)
(require redex)
(require "../refinementInference-VC-synth.rkt")
(require "../refinementInference.rkt")


(test-equal? "flatten-env"
        (term (flatten-env (x : Int (y : Bool (z : Int •)))))
        (term (x y z))
) 
(test-equal? "flatten-env"
        (term (flatten-env (x : Int (y : Bool •))))
        (term (x y))
) 
(test-equal? "flatten-env"
        (term (flatten-env •))
        (term ())
) 
(test-true 
"gen-fresh-template"
(redex-match?
        TypedLambda/Inference
    (Int (v : (q y (f z))))
    (term (gen-fresh-template (x : (Int {x : true}) •) (Int {HOLE hole-name})))
))