; A Language with Lazy Evaluation
#lang racket

(require (lib "eopl.ss" "eopl"))

(define-datatype environment environment?
  (empty-env)
  (extend-env (pre environment?) (var symbol?) (val (lambda (t) #t)))
  (extend-env-rec (pre environment?) (name (list-of symbol?)) (para (list-of symbol?)) (body (list-of expression?))))

(define location
  (lambda (lis var)
    (cond
      ((null? lis) #f)
      ((eqv? var (car lis)) 0)
      (else (let ([pos (location (cdr lis) var)])
              (if pos
                (add1 pos)
                #f))))))
          
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
        (eopl:error 'apply-env "No binding for ~s" search-var))
      (extend-env (pre var val)
        (if (eqv? search-var var)
          val
          (apply-env pre search-var)))
      (extend-env-rec (pre var para body)
        (let ([pos (location var search-var)])
          (if pos
            (newref (proc-val (procedure env (list-ref para pos) (list-ref body pos))))
            (apply-env pre search-var)))))))

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
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("begin" (arbno expression) "end") block-exp)
    (expression ("set!" identifier "=" expression) assign-exp)
    (expression ("letrec" (arbno identifier "(" identifier ")" "=" expression) "in" expression) letrec-exp)))

(sllgen:make-define-datatypes scanner-spec parser-spec)

(define scan&parse
  (sllgen:make-string-parser scanner-spec parser-spec))

(define procedure
  (lambda (env para body)
    (lambda (val)
      (value-of (extend-env env para val) body))))

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc procedure?)))

(define-datatype thunk thunk?
  (a-thunk (env environment?) (exp expression?)))

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

(define the-store '())

(define initialize-store!
  (lambda ()
    (set! the-store '())))

(define newref
  (lambda (val)
    (let ([ref (length the-store)])
      (set! the-store (append the-store (list val)))
      ref)))

(define deref
  (lambda (ref)
    (list-ref the-store ref)))

(define setref!
  (lambda (ref val)
    (set! the-store
      (letrec ([setref-inner
        (lambda (store ref1 val1)
          (if (zero? ref1)
            (cons val (cdr store))
            (cons (car store) (setref-inner (cdr store) (sub1 ref1) val))))])
        (setref-inner the-store ref val)))))

(define value-of-block
  (lambda (env block)
    (let ([first (car block)]
          [remain (cdr block)])
      (if (null? remain)
        (value-of env first)
        (begin
          (value-of env first)
          (value-of-block env remain))))))     

(define value-of
  (lambda (env pgm)
    (if (program? pgm)
      (cases program pgm
        (a-program (exp)
          (value-of env exp)))
      (cases expression pgm
        (const-exp (number)
          (num-val number))
        (diff-exp (exp-a exp-b)
          (let ([val-a (expval->num (value-of env exp-a))]
                [val-b (expval->num (value-of env exp-b))])
            (num-val (- val-a val-b))))
        (zero-exp (exp)
          (let ([val (expval->num (value-of env exp))])
            (if (zero? val)
              (bool-val #t)
              (bool-val false))))
        (if-exp (exp-if exp-then exp-else)
          (let ([val (expval->bool (value-of env exp-if))])
            (if val
              (value-of env exp-then)
              (value-of env exp-else))))
        (var-exp (var)
          (let* ([ref (apply-env env var)]
                 [val (deref ref)])
            (if (expval? val)
              val
              (cases thunk val
                (a-thunk (env exp)
                  (setref! ref (value-of env exp))
                  (deref ref))))))
        (let-exp (var exp body)
          (let ([val (value-of env exp)])
            (value-of (extend-env env var (newref val)) body)))
        (proc-exp (para body)
          (proc-val (procedure env para body)))
        (call-exp (exp arg)
          (let ([val-a (expval->proc (value-of env exp))]
                [val-b (cases expression arg
                         (var-exp (var) (apply-env env var))
                         (else (newref (a-thunk env arg))))])
            (val-a val-b)))
        (block-exp (block)
          (value-of-block env block))
        (assign-exp (var exp)
          (let ([val (value-of env exp)])
            (setref! (apply-env env var) val)
            val))
        (letrec-exp (var para body exp)
          (value-of (extend-env-rec env var para body) exp))))))
   
(define init-env (empty-env))
(set! init-env (extend-env init-env 'i (num-val 1)))
(set! init-env (extend-env init-env 'v (num-val 5)))
(set! init-env (extend-env init-env 'x (num-val 10)))

(define run
  (lambda (program)
    (value-of (empty-env) (scan&parse program))))

(initialize-store!)

(run "let makerec = proc (f)
                      let d = proc (m)
                                proc (n) ((f (m m)) n)
                        in proc (x) ((f (d d)) x)
        in let sum = proc (f)
                       proc (x)
                         if zero?(x)
                         then 0
                         else -((f -(x 1)) 4)
             in ((makerec sum) 4)")