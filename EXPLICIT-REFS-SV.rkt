; EXPLICIT-REFS-SV: A Language with Explicit References (the Store-passing Version)
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
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("(" expression "," expression ")") call-exp)
    (expression ("begin" expression (arbno ";" expression) "end") block-exp)
    (expression ("newref" "(" expression ")") newref-exp)
    (expression ("deref" "(" expression ")") deref-exp)
    (expression ("setref" "(" expression "," expression ")") setref-exp)))

(sllgen:make-define-datatypes scanner-spec parser-spec)

(define scan&parse
  (sllgen:make-string-parser scanner-spec parser-spec))

(define procedure
  (lambda (env para body)
    (lambda (store val)
      (value-of (extend-env env para val) store body))))

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc procedure?))
  (ref-val (int integer?)))

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

(define expval->ref
  (lambda (val)
    (cases expval val
      (ref-val (ref) ref)
      (else (eopl:error 'expval->ref "Bad conversion: ~s" val)))))

(define empty-store '())

(define value-of-block
  (lambda (env store block)
    (let ([first (car block)]
          [remain (cdr block)])
      (if (null? remain)
        (value-of env store first)
        (let* ([answer (value-of env store first)]
               [store-new (cadr answer)])
          (value-of-block env store-new remain))))))

(define value-of
  (lambda (env store pgm)
    (if (program? pgm)
      (cases program pgm
        (a-program (exp)
          (value-of env store exp)))
      (cases expression pgm
        (const-exp (number)
          (list (num-val number) store))
        (diff-exp (exp-a exp-b)
          (let* ([answer-a (value-of env store exp-a)]
                 [answer-b (value-of env (cadr answer-a) exp-b)]
                 [val-a (expval->num (car answer-a))]
                 [val-b (expval->num (car answer-b))])
            (list (num-val (- val-a val-b)) (cadr answer-b))))
        (zero-exp (exp)
          (let* ([answer (value-of env store exp)]
                 [val (expval->num (car answer))]
                 [store-new (cadr answer)])
            (if (zero? val)
              (list (bool-val #\t) store-new)
              (list (bool-val #\f) store-new))))
        (if-exp (exp-if exp-then exp-else)
          (let* ([answer-if (value-of env store exp-if)]
                 [val-if (expval->bool (car answer-if))]
                 [store-if (cadr answer-if)])
            (if (val-if)
              (value-of env store-if exp-then)
              (value-of env store-if exp-else))))
        (var-exp (var)
          (list (apply-env env var) store))
        (let-exp (var exp body)
          (let* ([answer (value-of env store exp)]
                 [val (car answer)]
                 [store-new (cadr answer)])
            (value-of (extend-env env var val) store-new body)))
        (proc-exp (para body)
          (list (proc-val (procedure env para body)) store))
        (call-exp (exp arg)
          (let* ([answer-exp (value-of env store exp)]
                 [val-exp (expval->proc (car answer-exp))]
                 [store-exp (cadr answer-exp)]
                 [answer-arg (value-of env store-exp arg)]
                 [val-arg (car answer-arg)]
                 [store-arg (cadr answer-arg)])
            (val-exp store-arg val-arg)))
        (block-exp (exp block)
          (value-of-block env store (cons exp block)))
        (newref-exp (exp)
          (let* ([answer (value-of env store exp)]
                 [val (car answer)]
                 [store-new (cadr answer)]
                 [ref (length store-new)])
            (list (ref-val ref) (append store-new (list val)))))
        (deref-exp (exp)
          (let* ([answer (value-of env store exp)]
                 [val (expval->ref (car answer))]
                 [store-new (cadr answer)])
            (list (list-ref store-new val) store-new)))
        (setref-exp (ref exp)
          (let* ([answer-ref (value-of env store ref)]
                 [val-ref (expval->ref (car answer-ref))]
                 [store-ref (cadr answer-ref)]
                 [answer-exp (value-of env store-ref exp)]
                 [val-exp (car answer-exp)]
                 [store-exp (cadr answer-exp)]
                 [store-new (setref store-exp val-ref val-exp)])
            (list val-exp store-new)))))))

(define setref
  (lambda (store ref val)
    (if (zero? ref)
      (cons val (cdr store))
      (cons (car store) (setref (cdr store) (sub1 ref) val)))))
      
(define init-env (empty-env))
(set! init-env (extend-env init-env 'i (num-val 1)))
(set! init-env (extend-env init-env 'v (num-val 5)))
(set! init-env (extend-env init-env 'x (num-val 10)))

(define run
  (lambda (program)
    (value-of init-env empty-store (scan&parse program))))

(run "let g = let counter = newref (0)
                in proc (dummy)
                  begin
                    setref(counter, -(deref(counter), 1));
                    deref (counter)
                  end
        in let a = (g, 11)
          in let b = (g, 11)
            in -(a, b)")