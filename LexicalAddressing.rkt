; A Language Implementing Lexical Addressing

#lang racket
(require (lib "eopl.ss" "eopl"))

(define empty-env
  (lambda () '()))

(define extend-env
  (lambda (env val) (cons val env)))

(define apply-env
  (lambda (env depth)
    (list-ref env depth)))
      
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
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)))

(sllgen:make-define-datatypes scanner-spec parser-spec)

(define scan&parse
  (sllgen:make-string-parser scanner-spec parser-spec))

(define-datatype nl-program nl-program?
  (nl-a-program (exp nl-expression?)))

(define-datatype nl-expression nl-expression?
  (nl-const-exp (num number?))
  (nl-diff-exp (exp1 nl-expression?) (exp2 nl-expression?))
  (nl-zero-exp (exp nl-expression?))
  (nl-if-exp (cond-exp nl-expression?) (then-exp nl-expression?) (else-exp nl-expression?))
  (nl-var-exp (depth number?))
  (nl-rec-var-exp (depth number?))
  (nl-let-exp (val nl-expression?) (body nl-expression?))
  (nl-letrec-exp (body nl-expression?) (exp nl-expression?))
  (nl-proc-exp (body nl-expression?))
  (nl-call-exp (rator nl-expression?) (rand nl-expression?)))

(define get-var-info
  (lambda (scope var)
    (if (null? scope)
      (eopl:error 'get-var-depth "No binding for ~s" var)
      (if (eqv? (cdr (car scope)) var)
        (cons (caar scope) 0)
        (let ([ret (get-var-info (cdr scope) var)])
          (cons (car ret) (add1 (cdr ret))))))))

(define translator
  (lambda (scope src)
    (if (program? src)
      (cases program src
        (a-program (exp)
          (nl-a-program (translator scope exp))))
      (cases expression src
        (const-exp (num)
          (nl-const-exp num))
        (diff-exp (exp1 exp2)
          (let ([nl-exp1 (translator scope exp1)]
                [nl-exp2 (translator scope exp2)])
            (nl-diff-exp nl-exp1 nl-exp2)))
        (zero-exp (exp)
          (nl-zero-exp (translator scope exp)))
        (if-exp (cond-exp then-exp else-exp)
          (let ([nl-cond-exp (translator scope cond-exp)]
                [nl-then-exp (translator scope then-exp)]
                [nl-else-exp (translator scope else-exp)])
            (nl-if-exp nl-cond-exp nl-then-exp nl-else-exp)))
        (var-exp (var)
          (let ([info (get-var-info scope var)])
            (if (eqv? (car info) 'rec)
              (nl-rec-var-exp (cdr info))
              (nl-var-exp (cdr info)))))
        (let-exp (var val body)
          (nl-let-exp (translator scope val) (translator (cons (cons 'nonrec var) scope) body)))
        (letrec-exp (var para body exp)
          (let ([new-scope1 (cons (cons 'nonrec para) (cons (cons 'rec var) scope))]
                [new-scope2 (cons (cons 'rec var) scope)])
            (nl-letrec-exp (translator new-scope1 body) (translator new-scope2 exp))))
        (proc-exp (var body)
          (nl-proc-exp (translator (cons (cons 'nonrec var) scope) body)))
        (call-exp (rator rand)
          (nl-call-exp (translator scope rator) (translator scope rand)))))))

(define procedure
  (lambda (env body)
    (lambda (val)
      (value-of (extend-env env val) body))))

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
    (empty-env)))
           
(define value-of
  (lambda (env para)
    (if (nl-program? para)
      (cases nl-program para
        (nl-a-program (exp)
          (value-of env exp)))
      (cases nl-expression para
        (nl-const-exp (num)
          (num-val num))
        (nl-diff-exp (exp1 exp2)
          (let ([num1 (expval->num (value-of env exp1))]
                [num2 (expval->num (value-of env exp2))])
            (num-val (- num1 num2))))
        (nl-zero-exp (exp)
          (if (zero? (expval->num (value-of env exp)))
            (bool-val #t)
            (bool-val #f)))
        (nl-if-exp (cond-exp then-exp else-exp)
          (if (expval->bool (value-of env cond-exp))
            (value-of env then-exp)
            (value-of env else-exp)))
        (nl-var-exp (depth)
          (apply-env env depth))
        (nl-rec-var-exp (depth)
          (let ([ret (apply-env env depth)])
            (proc-val (procedure (extend-env (car env) ret) (cdr ret)))))         
        (nl-let-exp (val body)
          (value-of (extend-env env (value-of env val)) body))
        (nl-letrec-exp (body exp)
          (value-of (extend-env env (cons env body)) exp))
        (nl-proc-exp (body)
          (proc-val (procedure env body)))
        (nl-call-exp (rator rand)
          ((expval->proc (value-of env rator)) (value-of env rand)))))))

(define run
  (lambda (str)
    (value-of '() (translator '() (scan&parse str)))))

(run "letrec double(x) = if zero?(x) then 0 else -((double -(x 1)) -(0 2)) in (double 6)")
































