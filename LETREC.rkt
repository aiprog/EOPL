; LETREC: A Language with Recursive Procedures

#lang racket
(require (lib "eopl.ss" "eopl"))

; Procedural representation of environments
#|(define empty-env
  (lambda ()
    (lambda (search-var)
      (eopl:error 'apply-env "No binding for ~s" search-var))))

(define extend-env
  (lambda (var val env)
    (lambda (search-var)
      (if (eqv? search-var var)
        val
        (apply-env env search-var)))))

(define extend-env-rec
  (lambda (name para body env)
    (let ([d
           (lambda (f)
             (lambda (search-var)
               (if (eqv? search-var name)
                 (proc-val (procedure para body (f f)))
                 (apply-env env search-var))))])      
    (lambda (search-var)
      (if (eqv? search-var name)
        (proc-val (procedure para body (d d)))
        (apply-env env search-var))))))

(define apply-env
  (lambda (env search-var)
    (env search-var)))|#

(define-datatype environment environment?
  (empty-env)
  (extend-env (var symbol?) (val expval?) (env environment?))
  (extend-env-rec (name symbol?) (para symbol?) (body expression?) (env environment?)))

(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
        (eopl:error 'apply-env "No binding for ~s" search-var))
      (extend-env (var val next-env)
        (if (eqv? var search-var)
          val
          (apply-env next-env search-var)))
      (extend-env-rec (name para body next-env)
        (if (eqv? name search-var)
          (proc-val (procedure para body env))
          (apply-env next-env search-var))))))
         
(define scanner-spec
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)))

(define parser-spec
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression ("-" "(" expression expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("letrec" identifier "(" identifier ")" "=" expression "in" expression) letrec-exp)
    (expression ("(" expression expression ")") call-exp)))

(sllgen:make-define-datatypes scanner-spec parser-spec)

(define scan&parse
  (sllgen:make-string-parser scanner-spec parser-spec))

(define procedure
  (lambda (var body env)
    (lambda (val)
      (value-of body (extend-env var val env)))))

(define proc?
  (lambda (proc)
    (procedure? proc)))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?)))

(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num)
        num)
      (else (eopl:error 'expval->num "Bad conversion: ~s" val)))))

(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool)
        bool)
      (else (eopl:error 'expval->bool "Bad conversion: ~s" val)))))

(define expval->proc
  (lambda (val)
    (cases expval val
      (proc-val (proc)
        proc)
      (else (eopl:error 'expval->proc "Bad conversion: ~s" val)))))

(define init-env
  (lambda ()
    (extend-env 'i (num-val 1)
      (extend-env 'v (num-val 5)
        (extend-env 'x (num-val 10)
          (empty-env))))))
           
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num)
        (num-val num))
      (diff-exp (exp1 exp2)
        (let ([num1 (expval->num (value-of exp1 env))]
              [num2 (expval->num (value-of exp2 env))])
          (num-val (- num1 num2))))
      (zero-exp (exp)
        (if (zero? (expval->num (value-of exp env)))
          (bool-val #t)
          (bool-val #f)))
      (if-exp (exp1 exp2 exp3)
        (if (expval->bool (value-of exp1 env))
          (value-of exp2 env)
          (value-of exp3 env)))
      (var-exp (var)
        (apply-env env var))
      (let-exp (var exp1 exp2)
        (let ([new-env (extend-env var (value-of exp1 env) env)])
          (value-of exp2 new-env)))
      (letrec-exp (name para body exp)
        (value-of exp (extend-env-rec name para body env)))
      (call-exp (rator rand)
        ((expval->proc (value-of rator env)) (value-of rand env))))))

(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp)
        (value-of exp (init-env))))))

(define run
  (lambda (str)
    (value-of-program (scan&parse str))))

(run "letrec double (x) = if zero?(x) then 0 else -((double -(x 1)) -(0 2)) in (double 6)")