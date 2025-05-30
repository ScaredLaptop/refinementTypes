#lang racket
(require rackunit)
(require redex)
(require "../refinementInference-VC-synth.rkt")
(require "../refinementInference.rkt")



(judgment-holds
    (synthesis-type
      (x : (Int {x : (< 0 x)}) (y : (Int {y : (= y 1)}) •))
      ((add x) y)
      (Int {v : (= v (+ x y))})
      ))

(judgment-holds
    (check-type
        •
        (λ (y) (λ (x) (if x then true else y)))
        ((y : (Bool {y : true})) -> ((x : (Bool {x : true})) -> (Bool {z : (= z (or x y))})))
    )
    )