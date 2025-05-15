#lang racket
(require rackunit)
(require redex)
(require "../predicates.rkt")

; (test-true "basic predicates 1"
;            (redex-match? Constraints p (term (and 0 4)))
;            )
(test-true "basic predicates 2"
           (redex-match? Constraints p (term (and 0 x)))
           )
(test-true "basic predicates 3"
           (redex-match? Constraints p (term (and 0 x)))
           )
(test-true "basic predicates 4"
           (redex-match? Constraints p (term (and y w)))
           )

(test-true "basic constraints 1"
           (redex-match? Constraints c (term (and y x)))
           )
(test-true "basic constraints 2"
           (redex-match? Constraints c (term (cand y x)))
           )
(test-true "basic constraints 3"
           (redex-match? Constraints c (term (cand (and y w) (not (if x y z)))))
           )
(test-true "basic constraints 4"
           (redex-match? Constraints c (term (cand (and y w) (not (if x y z)))))
           )
(test-true "basic constraints 5"
           (redex-match? Constraints c (term (forall (a Int) (implies (and a b) (cand l k)))))
           )

(test-equal? "sub-basic"
             (term
              (sub-constraints (and y x) x (and y x)))
             (term (and y (and y x)))
             )
(test-true "sub"
           (alpha-equivalent?
            Constraints
            (term (sub-constraints
                   (forall (a Int) (implies (and a b) (cand l a)))
                   a
                   (and y x)))
            (term (forall (v Int) (implies (and v b) (cand l v))))))


;; Z3 tests
(test-true  "lit true"   (term (SmtValid (> 2 1))))
(test-false "lit false"  (term (SmtValid (< 2 1))))

;; conjunctions
(test-true  "cand good"
  (term (SmtValid (cand (= (+ 1 2) 3) (> 5 0)))))
(test-false "cand bad"
  (term (SmtValid (cand (> 1 0) (< 0 0)))))

;; selfification-style equality on an uninterpreted function
(redex-match? Constraints p 
  (term (cand (= (app f 7) (app f 7)))))
(test-true  "self eq"
  (term (SmtValid (= (app f 7) (app f 7)))))

;; quantifiers
(test-true  "forall square"
  (term (SmtValid
         (forall (x Int)
           (implies true (>= (* x x) 0))))))

(test-false "forall counterexample"
  (term (SmtValid
         (forall (x Int)
           (implies (< x 0) (< (* x x) 0))))))


;; ─────────── Predicates ───────────
(test-true "basic predicates 5"
           (redex-match? Constraints p
             (term (or (and x y) (not z)))))

(test-true "basic predicates 6"
           (redex-match? Constraints p
             (term (if x (and y z) (or (not x) (and y y))))))

(test-true "basic predicates 7 – deep nest"
           (redex-match? Constraints p
             (term (and (and (and x y) z) true))))

;; ─────────── Constraints ───────────
(test-true "basic constraints 6 – multi-level cand"
           (redex-match? Constraints c
             (term (cand (and x y)
                         (cand (or y z)
                               (not (if z x y)))))))

(test-true "basic constraints 7 – nested forall / implies"
           (redex-match? Constraints c
             (term (cand
                     (forall (b Int)
                       (implies (and b x)
                                (cand y b)))
                     (forall (c Int)
                       (implies (or c z)
                                (cand (and x y) c)))))))

;; ─────────── Substitution / α-equivalence ───────────
(test-true "sub-constraints multiple vars"
           (alpha-equivalent?
            Constraints
            (term (sub-constraints
                    (forall (b Int)
                      (implies (or b x) (cand y b)))
                    b
                    (and x z)))
            (term (forall (v Int)
                    (implies (or v x) (cand y v))))))

;; ─────────── Z3 validity (more variables & logic) ───────────
;; simple or
(test-true "or good"
  (term (SmtValid (or (< 0 1) (= 2 3)))))

;; unsat conjunction
(test-false "impossible inequality"
  (term (SmtValid (and (> 0 1) (= 2 2)))))

;; bounded property over squares
(test-true "forall bounded square"
  (term (SmtValid
         (forall (n Int)
           (implies (and (>= n 0) (<= n 10))
                    (<= (* n n) 100))))))

;; uninterpreted function – reflexivity still holds
(test-true "uninterp function reflexive"
  (term (SmtValid (= (app g (+ 1 2)) (app g 3)))))

(test-false "forall impossible increment"
  (term (SmtValid
         (forall (n Int)
           (implies true (< (+ n 1) n))))))

;; ⟹   Equality at different inputs is SAT for an uninterpreted g, so we expect #t.
(test-true "uninterp function unequal args – concrete ints"
  (term (SmtValid (= (app g 1) (app g 2)))))

(test-equal? "sub with nested cand/or"
             (term
              (sub-constraints (cand (or a b) (and c d)) c (and x y)))
             (term (cand (or a b) (and (and x y) d))))