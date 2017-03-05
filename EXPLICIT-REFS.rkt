; EXPLICIT-REFS: A Language with Explicit References
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
    (lambda (val)
      (value-of (extend-env env para val) body))))

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

(define the-store '())

(define initialize-store!
  (lambda ()
    (set! the-store '())))

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
          (apply-env env var))
        (let-exp (var exp body)
          (let ([val (value-of env exp)])
            (value-of (extend-env env var val) body)))
        (proc-exp (para body)
          (proc-val (procedure env para body)))
        (call-exp (exp arg)
          (let ([val-a (expval->proc (value-of env exp))]
                [val-b (value-of env arg)])
            (val-a val-b)))
        (block-exp (exp block)
          (value-of-block env (cons exp block)))
        (newref-exp (exp)
          (let ([val (value-of env exp)]
                [ref (length the-store)])
            (set! the-store (append the-store (list val)))
            (ref-val ref)))
        (deref-exp (exp)
          (let ([val (value-of env exp)])
            (list-ref the-store (expval->ref val))))
        (setref-exp (ref exp)
          (let ([int (expval->ref (value-of env ref))]
                [val (value-of env exp)])
            (set! the-store (setref the-store int val))
            val))))))

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
    (value-of init-env (scan&parse program))))

(run "let g = let counter = newref (0)
                in proc (dummy)
                  begin
                    setref(counter, -(deref(counter), 1));
                    deref (counter)
                  end
        in let a = (g, 11)
          in let b = (g, 11)
            in -(a, b)")