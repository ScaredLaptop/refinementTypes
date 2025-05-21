#lang racket
(require redex racket/string ffi/unsafe
         ; "predicates.rkt" ; Assuming this is not strictly needed for this MWE
         "../../../project/racket-z3/racket-z3-lib/ffi/functions.rkt"
         "../../../project/racket-z3/racket-z3-lib/ffi/enums.rkt"
         "../../../project/racket-z3/racket-z3-lib/ffi/types.rkt")


(define abs-script
#<<SMT
(set-logic HORN)
(declare-rel k (Int Int))
(declare-var x Int)
(declare-var v Int)

(rule (=> (and (>= x 0) (= v x)) (k x v)))
(rule (=> (and (< x 0) (= v (- 0 x))) (k x v)))
(rule (=> (k x v) (>= v 0)))

(query k)
SMT
)
(define (dbg tag msg)
  (displayln (format "[~a] ~a" tag msg)))

(define (chc-sat? script)
  (dbg 'ffi "Z3_mk_config")
  (define cfg (_Z3_mk_config))
  (dbg 'ffi "Z3_mk_context")
  (define ctx (_Z3_mk_context cfg))
  (_Z3_del_config cfg)
  (when (not ctx) (error 'chc-sat? "Z3_mk_context returned NULL"))

  (dbg 'ffi "Z3_mk_fixedpoint")
  (define fp (_Z3_mk_fixedpoint ctx))
  (when (not fp) (error 'chc-sat? "Z3_mk_fixedpoint returned NULL"))

  (_Z3_fixedpoint_inc_ref ctx fp)

  (dbg 'SMT-LIB script)
  (dbg 'ffi "Z3_fixedpoint_from_string")
  (_Z3_fixedpoint_from_string ctx fp script)

  (when (not (eq? (_Z3_get_error_code ctx) 'Z3_OK))
    (define err-msg (_Z3_get_error_msg ctx (_Z3_get_error_code ctx)))
    (_Z3_fixedpoint_dec_ref ctx fp)
    (error 'chc-sat?
           (string-append "Z3 parsing error: " err-msg)))

  (dbg 'ffi "Z3_fixedpoint_get_answer")
  (define ans-ast (_Z3_fixedpoint_get_answer ctx fp))

  (when (not ans-ast) ; ans-ast can be NULL if there was an issue or query is malformed
    (define err-code (_Z3_get_error_code ctx))
    (define err-msg (if (eq? err-code 'Z3_OK)
                        "Query might be malformed or no answer available."
                        (_Z3_get_error_msg ctx err-code)))
    (_Z3_fixedpoint_dec_ref ctx fp)
    (error 'chc-sat? (format "Z3_fixedpoint_get_answer returned NULL. Error: ~a" err-msg)))

  (define ans-str (_Z3_ast_to_string ctx ans-ast))
  (dbg 'Z3 (string-append "Answer: " ans-str))
  (_Z3_fixedpoint_dec_ref ctx fp)
  (_Z3_del_context ctx)

  (cond [(string=? ans-str "sat")    #t]
        [(string=? ans-str "unsat")  #f]
        [(string=? ans-str "unknown") (error 'chc-sat? "Z3 returned unknown")]
        [else (error 'chc-sat? (format "Z3 returned unexpected answer: ~a" ans-str))]))

(chc-sat? abs-script)