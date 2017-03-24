; STMT-CPI: A Continuation-Passing Interpreter with Statements
#lang racket

(require (lib "eopl.ss" "eopl"))

(define-datatype environment environment?
  (empty-env)
  (extend-env (pre environment?) (var symbol?) (val (lambda (t) #t))))

(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
        (eopl:error 'apply-env "No binding for ~s" search-var))
      (extend-env (pre var val)
        (if (eqv? search-var var)
          val
          (apply-env pre search-var))))))

(define scanner-spec
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)))

(define parser-spec
  '((program (statement) a-program)
    (statement (identifier "=" expression) assign-stmt)
    (statement ("print" expression) print-stmt)
    (statement ("{" (arbno statement ";") "}") block-stmt)
    (statement ("if" expression "then" statement "else" statement) if-stmt)
    (statement ("while" expression statement) while-stmt)
    (statement ("var" identifier (arbno "," identifier) ";" statement) var-stmt)
    (expression (number) const-exp)
    (expression ("-" "(" expression expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero-exp)
    (expression ("not" "(" expression ")") not-exp)
    (expression (identifier) var-exp)))

(sllgen:make-define-datatypes scanner-spec parser-spec)

(define scan&parse
  (sllgen:make-string-parser scanner-spec parser-spec))

(define procedure
  (lambda (env para body)
    (lambda (val)
      (value-of-stmt (extend-env env para (newref val)) body))))

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?)))

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

(define-datatype continuation continuation?
  (end-cont)
  (diff1-cont (env environment?) (cont continuation?) (exp expression?))
  (diff2-cont (cont continuation?) (val expval?))
  (zero-cont (cont continuation?))
  (not-cont (cont continuation?))
  (assign-cont (env environment?) (cont continuation?) (var symbol?))
  (print-cont (cont continuation?))
  (block-cont (env environment?) (cont continuation?) (block list?))
  (if-cont (env environment?) (cont continuation?) (then-stmt statement?) (else-stmt statement?))
  (while-cont1 (env environment?) (cont continuation?) (exp expression?) (stmt statement?))
  (while-cont2 (env environment?) (cont continuation?) (exp expression?) (stmt statement?)))

(define apply-stmt-cont
  (lambda (cont)
    (cases continuation cont
      (end-cont () (void))
      (block-cont (env cont block)
        (if (null? block)
           (apply-stmt-cont cont)
           (value-of-stmt env (block-cont env cont (cdr block)) (car block))))
      (while-cont2 (env cont exp stmt)
        (value-of-exp env (while-cont1 env cont exp stmt) exp))
      (else eopl:error 'apply-stmt-cont "Bad continuation: ~s" cont))))

(define apply-exp-cont
  (lambda (cont val)
    (cases continuation cont
      (diff1-cont (env cont exp)
        (value-of-exp env (diff2-cont cont val) exp))
      (diff2-cont (cont val-a)
        (apply-exp-cont cont (num-val (- (expval->num val-a) (expval->num val)))))
      (zero-cont (cont)
        (apply-exp-cont cont (if (zero? (expval->num val)) (bool-val #t) (bool-val #f))))
      (not-cont (cont)
        (apply-exp-cont cont (bool-val (not (expval->bool val)))))
      (assign-cont (env cont var)
        (begin
          (setref! (apply-env env var) val)
          (apply-stmt-cont cont)))
      (print-cont (cont)
        (begin
          (display val)
          (apply-stmt-cont cont)))
      (if-cont (env cont then-stmt else-stmt)
        (if (expval->bool val)
          (value-of-stmt env cont then-stmt)
          (value-of-stmt env cont else-stmt)))
      (while-cont1 (env cont exp stmt)
        (if (expval->bool val)
           (value-of-stmt env (while-cont2 env cont exp stmt) stmt)
           (apply-stmt-cont cont)))
      (else eopl:error 'apply-exp-cont "Bad continuation: ~s" cont))))

(define declare-var-list
  (lambda (env var)
    (if (null? var)
      env
      (declare-var-list (extend-env env (car var) (newref (num-val 0))) (cdr var)))))

(define value-of-pgm
  (lambda (env cont pgm)
    (cases program pgm
      (a-program (stmt)
        (value-of-stmt env cont stmt)))))

(define value-of-stmt
  (lambda (env cont stmt)
    (cases statement stmt
      (assign-stmt (var exp)
        (value-of-exp env (assign-cont env cont var) exp))
      (print-stmt (exp)
        (value-of-exp env (print-cont cont) exp))
      (block-stmt (block)
        (value-of-stmt env (block-cont env cont (cdr block)) (car block)))
      (if-stmt (if-exp then-exp else-exp)
        (value-of-exp env (if-cont env cont then-exp else-exp) if-exp))
      (while-stmt (exp stmt)
        (value-of-exp env (while-cont1 env cont exp stmt) exp))
      (var-stmt (var var-list stmt)
        (value-of-stmt (declare-var-list env (cons var var-list)) cont stmt)))))

(define value-of-exp
  (lambda (env cont exp)
    (cases expression exp
      (const-exp (number)
        (apply-exp-cont cont (num-val number)))
      (diff-exp (exp-a exp-b)
        (value-of-exp env (diff1-cont env cont exp-b) exp-a))
      (zero-exp (exp)
        (value-of-exp env (zero-cont cont) exp))
      (not-exp (exp)
        (value-of-exp env (not-cont cont) exp))
      (var-exp (var)
        (apply-exp-cont cont (deref (apply-env env var)))))))

(define run
  (lambda (program)
    (value-of-pgm (empty-env) (end-cont) (scan&parse program))))

(initialize-store!)

(run "var x, y;
      {
        x = 0;
        y = 3;
        while not(zero?(y))
        {
          x = -(x -(0 y));
          y = -(y 1);
        };
        print x;
      }")