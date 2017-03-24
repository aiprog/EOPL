; LETREC-CPI: A Continuation-Passing Interpreter

#lang racket
(require (lib "eopl.ss" "eopl"))

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
    (expression ("(" expression expression ")") call-exp)
    (expression ("list" "(" (arbno expression) ")") list-exp)))

(sllgen:make-define-datatypes scanner-spec parser-spec)

(define scan&parse
  (sllgen:make-string-parser scanner-spec parser-spec))

(define procedure
  (lambda (var body env)
    (lambda (cont val)
      (value-of (extend-env var val env) cont body))))

(define proc?
  (lambda (proc)
    (procedure? proc)))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?))
  (list-val
   (lis list?)))

(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (eopl:error 'expval->num "Bad conversion: ~s" val)))))

(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (eopl:error 'expval->bool "Bad conversion: ~s" val)))))

(define expval->proc
  (lambda (val)
    (cases expval val
      (proc-val (proc) proc)
      (else (eopl:error 'expval->proc "Bad conversion: ~s" val)))))

(define expval->list
  (lambda (val)
    (cases expval val
      (list-val (lis) lis)
      (else (eopl:error 'expval->lis "Bad conversion: ~s" val)))))

(define init-env
  (lambda ()
    (extend-env 'i (num-val 1)
      (extend-env 'v (num-val 5)
        (extend-env 'x (num-val 10)
          (empty-env))))))

(define-datatype continuation continuation?
  (end-cont)
  (diff1-cont (env environment?) (cont continuation?) (exp expression?))
  (diff2-cont (cont continuation?) (val expval?))
  (zero-cont (cont continuation?))
  (if-cont (env environment?) (cont continuation?) (exp2 expression?) (exp3 expression?))
  (let-cont (env environment?) (cont continuation?) (var symbol?) (exp2 expression?))
  (call-cont1 (env environment?) (cont continuation?) (rand expression?))
  (call-cont2 (cont continuation?) (val expval?))
  (list-cont (env environment?) (const continuation?) (exp list?) (val-list list?))) 

(define apply-cont
  (lambda (cont val)
    (cases continuation cont
      (end-cont () val)
      (diff1-cont (env cont exp)
        (value-of env (diff2-cont cont val) exp))
      (diff2-cont (cont val1)
        (apply-cont cont (num-val (- (expval->num val1) (expval->num val)))))
      (zero-cont (cont)
        (apply-cont cont (bool-val (zero? (expval->num val)))))
      (if-cont (env cont exp2 exp3)
        (if (expval->bool val)
          (value-of env cont exp2)
          (value-of env cont exp3)))
      (let-cont (env cont var exp2)  
        (value-of (extend-env var val env) cont exp2))
      (call-cont1 (env cont rand)
        (value-of env (call-cont2 cont val) rand))
      (call-cont2 (cont rator)
        ((expval->proc rator) cont val))
      (list-cont (env cont exp val-list)
        (let ([new-val-list (append val-list (list val))])
          (if (null? exp)
            (apply-cont cont (list-val new-val-list))
            (value-of env (list-cont env cont (cdr exp) new-val-list) (car exp))))))))
   
(define value-of
  (lambda (env cont exp)
    (cases expression exp
      (const-exp (num)
        (apply-cont cont (num-val num)))
      (diff-exp (exp1 exp2)
        (value-of env (diff1-cont env cont exp2) exp1))
      (zero-exp (exp)
        (value-of env (zero-cont cont) exp))
      (if-exp (exp1 exp2 exp3)
        (value-of env (if-cont env cont exp2 exp3) exp1))
      (var-exp (var)
        (apply-cont cont (apply-env env var)))
      (let-exp (var exp1 exp2)
        (value-of env (let-cont env cont var exp2) exp1))
      (letrec-exp (name para body exp)
        (value-of (extend-env-rec name para body env) cont exp))
      (call-exp (rator rand)
        (value-of env (call-cont1 env cont rand) rator))
      (list-exp (exp)
        (if (null? exp)
          (apply-cont cont (list-val '()))
          (value-of env (list-cont env cont (cdr exp) '()) (car exp)))))))

(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp)
        (value-of (init-env) (end-cont) exp)))))

(define run
  (lambda (str)
    (value-of-program (scan&parse str))))

;(run "letrec double (x) = if zero?(x) then 0 else -((double -(x 1)) -(0 2)) in (double 6)")
(run "let a = 1 in let b = 2 in list(a b -(a b))")