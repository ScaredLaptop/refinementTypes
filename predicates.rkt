#lang racket
(require redex racket/string racket/syntax)
;; Ensure these paths are correct for your project structure
(require "../../../project/racket-z3/racket-z3-lib/ffi/functions.rkt")
(require "../../../project/racket-z3/racket-z3-lib/ffi/enums.rkt")
(require "../../../project/racket-z3/racket-z3-lib/ffi/types.rkt")


(define-language Constraints
  ((x y z)   variable-not-otherwise-mentioned)
  ((f g)   variable-not-otherwise-mentioned) ; For uninterpreted function symbols
  (bool true false)
  (int  integer)
  (op   + - * / = < > <= >=)
  (b    Bool Int)

  (p ::=
     x y z
     bool
     int
     (op p p)
     (and p p)
     (or  p p)
     (not p)
     (if p p p)
     (app f p))

  (c ::=
     p
     (cand c c)
     (forall (x b) (implies p c)))

  #:binding-forms
  (forall (x b) _ #:refers-to x))

(define-metafunction Constraints
  sub-constraints : c x c -> c
  [(sub-constraints c_1 x_1 c_2) (substitute c_1 x_1 c_2)]
)

(define (dbg tag msg)
  (displayln (format "[~a] ~a" tag msg)))

(define (symbol->smt-base-name rkt-symbol)
  (define raw-str (symbol->string rkt-symbol))
  (car (string-split raw-str "«")))

(define interpreted-ops '(+ - * / = < > <= >=))

(define (compile-c term)
  (match term
    [(? symbol? v-sym) (symbol->smt-base-name v-sym)]
    [(? boolean?  b)   (if b "true" "false")]
    [(? integer?  n)   (number->string n)]

    [(list 'not  p)    (format "(not ~a)"  (compile-c p))]
    [(list 'and  p q)  (format "(and ~a ~a)" (compile-c p) (compile-c q))]
    [(list 'or   p q)  (format "(or  ~a ~a)"  (compile-c p) (compile-c q))]
    [(list 'if   g t e)(format "(ite ~a ~a ~a)"
                               (compile-c g) (compile-c t) (compile-c e))]
    [(list 'cand c1 c2)(format "(and ~a ~a)"
                               (compile-c c1) (compile-c c2))]
    [(list 'implies p q)(format "(=> ~a ~a)"
                               (compile-c p) (compile-c q))]

    [(list 'forall (list x-original-sym b-type) (list 'implies p-guard body-c))
     (define smt-binder-str (symbol->smt-base-name x-original-sym))
     (format "(forall ((~a ~a)) (=> ~a ~a))"
             smt-binder-str
             (if (eq? b-type 'Bool) "Bool" "Int")
             (compile-c p-guard)
             (compile-c body-c))]

    [(list 'app f-sym p-arg)
     (format "(~a ~a)" (symbol->smt-base-name f-sym) (compile-c p-arg))]

    [(list (and op-sym (? (lambda (s) (memq s interpreted-ops)))) p1 p2)
     (format "(~a ~a ~a)"
             (symbol->string op-sym) (compile-c p1) (compile-c p2))]
    [_ (error 'compile-c "unknown constraint pattern: ~a" term)]))


(define (collect-app-funs term)
  (match term
    [(list 'app f-sym p-arg)   (cons f-sym (collect-app-funs p-arg))]
    [(list _head rst ...)      (apply append (map collect-app-funs rst))]
    [_                         '()]))

(define (smt-pieces term)
  (values
   (string-join
    (for/list ([f-sym (in-list (remove-duplicates (collect-app-funs term)))])
      (format "(declare-fun ~a (Int) Int)" (symbol->smt-base-name f-sym)))
    "\n")
   (compile-c term)))

(define (smt-script term)
  (define-values (decls formulas) (smt-pieces term))
  (string-join
   (filter non-empty-string?
           (list decls
                 (format "(assert ~a)" formulas)
                 "(check-sat)"))
   "\n"))

(define z3-ctx
  (let ([cfg (_Z3_mk_config)])
    (_Z3_set_param_value cfg "model" "false")
    (define ctx (_Z3_mk_context cfg))
    (_Z3_del_config cfg)
    ctx))

(define (z3-sat? redex-constraint-term)
  (define-values (decls term-str) (smt-pieces redex-constraint-term))
  (define full-script
    (string-join
     (filter non-empty-string?
             (append
              (if (not (non-empty-string? decls)) '() (list decls))
              (list (format "(assert ~a)" term-str)
                    "(check-sat)")))
     "\n"))

  (dbg 'SMT-LIB full-script)

  (define cfg (_Z3_mk_config)) (dbg 'ffi "Z3_mk_config")
  (_Z3_set_param_value cfg "model" "false") (dbg 'ffi "Z3_set_param_value")
  (define ctx (_Z3_mk_context cfg)) (dbg 'ffi "Z3_mk_context")
  (_Z3_del_config cfg) (dbg 'ffi "Z3_del_config")
  (define solver (_Z3_mk_solver ctx)) (dbg 'ffi "Z3_mk_solver")

  (_Z3_solver_from_string ctx solver full-script)
  (dbg 'ffi "Z3_solver_from_string")
  (when (not (eq? (_Z3_get_error_code ctx) 'Z3_OK))
    (error 'z3-sat? "Z3 parsing error: ~a" (_Z3_get_error_msg ctx (_Z3_get_error_code ctx))))

  (define res (_Z3_solver_check ctx solver))
  (dbg 'ffi "Z3_solver_check")
  (when (not (eq? (_Z3_get_error_code ctx) 'Z3_OK))
    (error 'z3-sat? "Z3 solver error: ~a" (_Z3_get_error_msg ctx (_Z3_get_error_code ctx))))
  (dbg 'ffi (string-append "Z3 Returned: " (if (equal? res 'Z3_L_TRUE)
                                                "Z3_L_TRUE"
                                                (if (equal? res 'Z3_L_FALSE)
                                                    "Z3_L_FALSE"
                                                    (if (equal? res 'Z3_L_UNDEF)
                                                        "Z3_L_UNDEF"
                                                        (format "Unknown result: ~a" res))))))
  (equal? res 'Z3_L_TRUE))

(define-metafunction Constraints
  SmtValid : c -> #t or #f
  [(SmtValid c_1) ,(z3-sat? (term c_1))]
)

(provide Constraints sub-constraints SmtValid compile-c smt-script)