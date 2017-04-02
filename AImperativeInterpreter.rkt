; A Imperative Interpreter

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
          (proc-val (procedure para body))
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
  (lambda (var body)
    (lambda ()
      (begin
        (set! env (extend-env var val env))
        (set! exp body)
        value-of))))

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
  (call-cont2 (env environment?) (cont continuation?) (val expval?))) 

(define env 'uninitialized)
(define cont 'uninitialized)
(define exp 'uninitialized)
(define val 'uninitialized)

(define apply-cont
  (lambda ()
    (cases continuation cont
      (end-cont () val)
      (diff1-cont (env1 cont1 exp1)
        (begin
          (set! env env1)
          (set! cont (diff2-cont cont1 val))
          (set! exp exp1)
          value-of))
      (diff2-cont (cont1 val1)
        (begin
          (set! cont cont1)
          (set! val (num-val (- (expval->num val1) (expval->num val))))
          apply-cont))
      (zero-cont (cont1)
        (begin
          (set! cont cont1)
          (set! val (if (zero? (expval->num val)) (bool-val #t) (bool-val #f)))
          apply-cont))
      (if-cont (env1 cont1 exp2 exp3)
        (begin
          (set! env env1)
          (set! cont cont1)
          (set! exp (if (expval->bool val) exp2 exp3))
          value-of))
      (let-cont (env1 cont1 var exp1)  
        (begin
          (set! env (extend-env var val env1))
          (set! cont cont1)
          (set! exp exp1)
          value-of))
      (call-cont1 (env1 cont1 rand)
        (begin
          (set! env env1)
          (set! cont (call-cont2 env1 cont1 val))
          (set! exp rand)
          value-of))
      (call-cont2 (env1 cont1 rator)
        (begin
          (set! env env1)
          (set! cont cont1)
          (expval->proc rator))))))

(define value-of
  (lambda ()
    (cases expression exp
      (const-exp (num)
        (begin
          (set! val (num-val num))
          apply-cont))
      (diff-exp (exp1 exp2)
        (begin
          (set! cont (diff1-cont env cont exp2))
          (set! exp exp1)
          value-of))
      (zero-exp (exp1)
        (begin
          (set! cont (zero-cont cont))
          (set! exp exp1)
          value-of))
      (if-exp (exp1 exp2 exp3)
        (begin
          (set! cont (if-cont env cont exp2 exp3))
          (set! exp exp1)
          value-of))
      (var-exp (var)
        (begin
          (set! val (apply-env env var))
          apply-cont))
      (let-exp (var exp1 exp2)
        (begin
          (set! cont (let-cont env cont var exp2))
          (set! exp exp1)
          value-of))
      (letrec-exp (name para body exp1)
        (begin
          (set! env (extend-env-rec name para body env))
          (set! exp exp1)
          value-of))
      (call-exp (rator rand)
        (begin
          (set! cont (call-cont1 env cont rand))
          (set! exp rator)
          value-of)))))

(define trampoline
  (lambda (var)
    (if (expval? var) var (trampoline (var)))))

(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
        (begin
          (set! env (init-env))
          (set! cont (end-cont))
          (set! exp exp1)
          (trampoline value-of))))))

(define run
  (lambda (str)
    (value-of-program (scan&parse str))))

(run "let inc = 2 in letrec double (x) = if zero?(x) then 0 else -((double -(x 1)) -(0 inc)) in let inc = 3 in (double 6)")
;(run "let a = 1 in let b = 2 in list(a b -(a b))")