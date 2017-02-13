; LET: A Simple Language

#lang racket
(require (lib "eopl.ss" "eopl"))

(define empty-env
  (lambda () (list 'empty-env)))

(define extend-env
  (lambda (var val env) (list 'extend-env var val env)))

(define apply-env
  (lambda (env search-var)
    (cond
      ((eqv? (car env) 'empty-env)
       (eopl:error 'apply-env "No binding for ~s" search-var))
      ((eqv? (car env) 'extend-env)
       (if (eqv? (cadr env) search-var)
         (caddr env)
         (apply-env (cadddr env) search-var)))
      (else
       (eopl:error 'apply-env "Bad environment: ~s" env)))))

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
    (expression ("let" identifier "=" expression "in" expression) let-exp)))

(sllgen:make-define-datatypes scanner-spec parser-spec)

(define scan&parse
  (sllgen:make-string-parser scanner-spec parser-spec))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?)))

(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num)
        num)
      (bool-val (bool)
        (eopl:error 'expval->num "Bad conversion: ~s" val)))))

(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool)
        bool)
      (num-val (num)
        (eopl:error 'expval->bool "Bad conversion: ~s" val)))))

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
          (value-of exp2 new-env))))))

(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp)
        (value-of exp (init-env))))))

(define run
  (lambda (str)
    (value-of-program (scan&parse str))))

(run "let a = 1 in if zero? (-(a i)) then -(5 3) else -(3 5)")