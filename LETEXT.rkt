; LETEXT: Extended LET according to exercises

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
    (expression ("minus" "(" expression ")") minus-exp)
    (expression ("+" "(" expression expression ")") add-exp)
    (expression ("-" "(" expression expression ")") diff-exp)
    (expression ("*" "(" expression expression ")") mul-exp)
    (expression ("/" "(" expression expression ")") div-exp)
    (expression ("equal?" "(" expression expression ")") eq-exp)
    (expression ("greater?" "(" expression expression ")") gt-exp)
    (expression ("less?" "(" expression expression ")") lt-exp)
    (expression ("zero?" "(" expression ")") zero-exp)
    (expression ("cons" "(" expression expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("null?" "(" expression ")") null-exp)
    (expression ("emptylist") empty-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("cond" (arbno expression "==>" expression) "end") cond-exp)
    (expression (identifier) var-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("let*" (arbno identifier "=" expression) "in" expression) let*-exp)
    (expression ("unpack" (arbno identifier) "=" expression "in" expression) unpack-exp)))

(sllgen:make-define-datatypes scanner-spec parser-spec)

(define scan&parse
  (sllgen:make-string-parser scanner-spec parser-spec))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (list-val
   (lis list?)))

(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num)
        num)
      (else
        (eopl:error 'expval->num "Bad conversion: ~s" val)))))

(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool)
        bool)
      (else
        (eopl:error 'expval->bool "Bad conversion: ~s" val)))))

(define expval->list
  (lambda (val)
    (cases expval val
      (list-val (lis)
        lis)
      (else
       (eopl:error 'expval->list "Bad conversion: ~s" val)))))

(define init-env
  (lambda ()
    (extend-env 'i (num-val 1)
      (extend-env 'v (num-val 5)
        (extend-env 'x (num-val 10)
          (empty-env))))))

(define let-new-env
  (lambda (var exp env new-env)
    (if (null? var)
        new-env
        (let-new-env (cdr var) (cdr exp) env
          (extend-env (car var) (value-of (car exp) env) new-env)))))

(define unpack-new-env
  (lambda (var val env)
    (if (null? var)
        (if (not (null? (expval->list val)))
            (eopl:error 'unpack-exp "Numbers don't match")
            env)
        (unpack-new-env (cdr var) (list-val (cdr (expval->list val)))
          (extend-env (car var) (car (expval->list val)) env)))))

(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num)
        (num-val num))
      (minus-exp (exp)
        (num-val (- (expval->num (value-of exp env)))))
      (add-exp (exp1 exp2)
        (let ([num1 (expval->num (value-of exp1 env))]
              [num2 (expval->num (value-of exp2 env))])
          (num-val (+ num1 num2))))
      (diff-exp (exp1 exp2)
        (let ([num1 (expval->num (value-of exp1 env))]
              [num2 (expval->num (value-of exp2 env))])
          (num-val (- num1 num2))))
      (mul-exp (exp1 exp2)
        (let ([num1 (expval->num (value-of exp1 env))]
              [num2 (expval->num (value-of exp2 env))])
          (num-val (* num1 num2))))
      (div-exp (exp1 exp2)
        (let ([num1 (expval->num (value-of exp1 env))]
              [num2 (expval->num (value-of exp2 env))])
          (num-val (/ num1 num2))))
      (eq-exp (exp1 exp2)
        (let ([num1 (expval->num (value-of exp1 env))]
              [num2 (expval->num (value-of exp2 env))])
          (bool-val (= num1 num2))))
      (gt-exp (exp1 exp2)
        (let ([num1 (expval->num (value-of exp1 env))]
              [num2 (expval->num (value-of exp2 env))])
          (bool-val (> num1 num2))))
      (lt-exp (exp1 exp2)
        (let ([num1 (expval->num (value-of exp1 env))]
              [num2 (expval->num (value-of exp2 env))])
          (bool-val (< num1 num2))))
      (zero-exp (exp)
        (if (zero? (expval->num (value-of exp env)))
          (bool-val #t)
          (bool-val #f)))
      (cons-exp (exp1 exp2)
        (let ([val1 (value-of exp1 env)]
              [val2 (value-of exp2 env)])
          (list-val (cons val1 (expval->list val2)))))
      (car-exp (exp)
        (car (expval->list (value-of exp env))))
      (cdr-exp (exp)
        (cdr (expval->list (value-of exp env))))
      (null-exp (exp)
        (bool-val (null? (expval->list (value-of exp env)))))
      (empty-exp ()
        (list-val '()))
      (if-exp (exp1 exp2 exp3)
        (if (expval->bool (value-of exp1 env))
          (value-of exp2 env)
          (value-of exp3 env)))
      (cond-exp (lis1 lis2)
        (if (null? lis1)
          (eopl:error 'cond-exp "No true value in cond-exp")
          (if (expval->bool (value-of (car lis1) env))
              (value-of (car lis2) env)
              (value-of (cond-exp (cdr lis1) (cdr lis2)) env))))
      (var-exp (var)
        (apply-env env var))
      (let-exp (var exp1 exp2)
        (value-of exp2 (let-new-env var exp1 env env)))
      (let*-exp (var exp1 exp2)
        (if (null? var)
            (value-of exp2 env)
            (value-of (let*-exp (cdr var) (cdr exp1) exp2)
              (extend-env (car var) (value-of (car exp1) env) env))))
      (unpack-exp (var exp1 exp2)
        (value-of exp2 (unpack-new-env var (value-of exp1 env) env))))))

(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp)
        (value-of exp (init-env))))))

(define run
  (lambda (str)
    (value-of-program (scan&parse str))))

(run "let u = 7 in unpack x y = cons (u cons (3 emptylist)) in - (x y)")