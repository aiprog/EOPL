; PROCEXT: Extended PROC according to exercises

#lang racket
(require (lib "eopl.ss" "eopl"))

(define empty-env
  (lambda () (list 'empty-env)))

(define extend-env
  (lambda (var val env) (list 'extend-env var val env)))

(define extend-env*
  (lambda (var val env)
    (if (null? var)
      env
      (extend-env* (cdr var) (cdr val)
        (extend-env (car var) (car val) env)))))

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
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)))

(sllgen:make-define-datatypes scanner-spec parser-spec)

(define scan&parse
  (sllgen:make-string-parser scanner-spec parser-spec))

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

(define procedure
  (lambda (var body env)
    (lambda (val)
      (begin
        (display "enter procedure\n")
        (let ([ret (value-of body (extend-env* var val env))])
          (display "leave procedure\n")
          ret)))))

(define proc?
  (lambda (proc)
    (procedure? proc)))

(define get-free-var
  (lambda (exp)
    (cases expression exp
      (const-exp (num)
        '())
      (diff-exp (exp1 exp2)
        (let ([var1 (get-free-var exp1)]
              [var2 (get-free-var exp2)])
          (remove-duplicates (append var1 var2))))
      (zero-exp (exp)
        (get-free-var (exp)))
      (if-exp (exp1 exp2 exp3)
        (let ([var1 (get-free-var exp1)]
              [var2 (get-free-var exp2)]
              [var3 (get-free-var exp3)])
          (remove-duplicates (append var1 (append var2 var3)))))
      (var-exp (var)
        (list var))
      (let-exp (var exp1 exp2)
        (let ([var1 (get-free-var exp1)]
              [var2 (get-free-var exp2)])
          (remove-duplicates (append var1 (remove var var2)))))
      (proc-exp (var body)
        (remove* var (get-free-var body)))
      (call-exp (rator rand)
        (let ([var1 (get-free-var rator)]
              [var2 (get-free-var* rand)])
          (remove-duplicates (append var1 var2)))))))

(define get-free-var*
  (lambda (exp)
    (if (null? exp)
        '()
        (remove-duplicates (append (get-free-var (car exp)) (get-free-var* (cdr exp)))))))

(define simplify-proc-env
  (lambda (var env)
    (if (null? var)
      (empty-env)
      (extend-env (car var) (apply-env env (car var))
        (simplify-proc-env (cdr var) env)))))

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
      (proc-exp (var body)
        (proc-val (procedure var body (simplify-proc-env (get-free-var exp) env))))
      (call-exp (rator rand)
        ((expval->proc (value-of rator env)) (value-of* rand env))))))

(define value-of*
  (lambda (exp env)
    (if (null? exp)
      '()
      (cons (value-of (car exp) env) (value-of* (cdr exp) env)))))

(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp)
        (value-of exp (init-env))))))

(define run
  (lambda (str)
    (value-of-program (scan&parse str))))

(run "let f1 = proc (a) -(a 1)
        in let f2 = proc (b) -(b (f1 2))
          in (f2 3)")