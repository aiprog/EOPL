; Lexical Addressing with Letrec and Trimmed Representation of Procedures

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
  (nl-var-exp (var symbol?) (depth vector?))
  (nl-rec-var-exp (var symbol?) (depth vector?))
  (nl-let-exp (var symbol?) (val nl-expression?) (body nl-expression?))
  (nl-letrec-exp (var symbol?) (para symbol?) (body nl-expression?) (exp nl-expression?) (data vector?))
  (nl-proc-exp (para symbol?) (body nl-expression?) (data vector?))
  (nl-call-exp (rator nl-expression?) (rand nl-expression?)))

(define get-var-info
  (lambda (scope var)
    (if (null? scope)
      (eopl:error 'get-var-depth "No binding for ~s" var)
      (if (eqv? (cdr (car scope)) var)
        (cons (caar scope) 0)
        (let ([ret (get-var-info (cdr scope) var)])
          (cons (car ret) (add1 (cdr ret))))))))

(define translator-s1
  (lambda (scope src)
    (if (program? src)
      (cases program src
        (a-program (exp)
          (nl-a-program (translator-s1 scope exp))))
      (cases expression src
        (const-exp (num)
          (nl-const-exp num))
        (diff-exp (exp1 exp2)
          (let ([nl-exp1 (translator-s1 scope exp1)]
                [nl-exp2 (translator-s1 scope exp2)])
            (nl-diff-exp nl-exp1 nl-exp2)))
        (zero-exp (exp)
          (nl-zero-exp (translator-s1 scope exp)))
        (if-exp (cond-exp then-exp else-exp)
          (let ([nl-cond-exp (translator-s1 scope cond-exp)]
                [nl-then-exp (translator-s1 scope then-exp)]
                [nl-else-exp (translator-s1 scope else-exp)])
            (nl-if-exp nl-cond-exp nl-then-exp nl-else-exp)))
        (var-exp (var)
          (let ([info (get-var-info scope var)])
            (if (eqv? (car info) 'rec)
              (nl-rec-var-exp var (make-vector 1))
              (nl-var-exp var (make-vector 1)))))
        (let-exp (var val body)
          (nl-let-exp var (translator-s1 scope val) (translator-s1 (cons (cons 'nonrec var) scope) body)))
        (letrec-exp (var para body exp)
          (let ([new-scope1 (cons (cons 'nonrec para) (cons (cons 'rec var) scope))]
                [new-scope2 (cons (cons 'rec var) scope)])
            (nl-letrec-exp var para (translator-s1 new-scope1 body) (translator-s1 new-scope2 exp) (make-vector 1))))
        (proc-exp (para body)
          (nl-proc-exp para (translator-s1 (cons (cons 'nonrec para) scope) body) (make-vector 1)))
        (call-exp (rator rand)
          (nl-call-exp (translator-s1 scope rator) (translator-s1 scope rand)))))))

(define translator-s2
  (lambda (src)
    (if (nl-program? src)
      (cases nl-program src
        (nl-a-program (exp)
          (translator-s2 exp)))
      (cases nl-expression src
        (nl-const-exp (num)
          '())
        (nl-diff-exp (exp1 exp2)
          (remove-duplicates (append (translator-s2 exp1) (translator-s2 exp2))))
        (nl-zero-exp (exp)
          (translator-s2 exp))
        (nl-if-exp (cond-exp then-exp else-exp)
          (remove-duplicates (append (translator-s2 cond-exp) (translator-s2 then-exp) (translator-s2 else-exp))))
        (nl-rec-var-exp (var depth)
          '())
        (nl-var-exp (var depth)
          (list var))
        (nl-let-exp (var val body)
           (remove-duplicates (append (translator-s2 val) (remove var (translator-s2 body)))))
        (nl-letrec-exp (var para body exp data)
          (let ([ret1 (remove* (list var para) (translator-s2 body))]
                [ret2 (remove var (translator-s2 exp))])
            (vector-set! data 0 ret1)
            (remove-duplicates (append ret1 ret2))))
        (nl-proc-exp (para body data)
          (vector-set! data 0 (remove para (translator-s2 body)))
          (vector-ref data 0))
        (nl-call-exp (rator rand)
          (remove-duplicates (append (translator-s2 rator) (translator-s2 rand))))))))

(define var-to-pos
  (lambda (scope var)
    (if (null? var)
      '()
      (cons (cdr (get-var-info scope (car var))) (var-to-pos scope (cdr var))))))

(define var-to-scope
  (lambda (var)
    (if (null? var)
      '()
      (cons (cons 'nonrec (car var)) (var-to-scope (cdr var))))))

(define env-from-pos
  (lambda (env pos)
    (if (null? pos)
      '()
      (cons (list-ref env (car pos)) (env-from-pos env (cdr pos))))))

(define translator-s3
  (lambda (scope src)
    (if (nl-program? src)
      (cases nl-program src
        (nl-a-program (exp)
          (translator-s3 scope exp)))
      (cases nl-expression src
        (nl-const-exp (num)
          '())
        (nl-diff-exp (exp1 exp2)
          (translator-s3 scope exp1)
          (translator-s3 scope exp2))
        (nl-zero-exp (exp)
          (translator-s3 scope exp))
        (nl-if-exp (cond-exp then-exp else-exp)
          (translator-s3 scope cond-exp)
          (translator-s3 scope then-exp)
          (translator-s3 scope else-exp))
        (nl-rec-var-exp (var depth)
          (let ([info (get-var-info scope var)])
            (vector-set! depth 0 (cdr info))))
        (nl-var-exp (var depth)
          (let ([info (get-var-info scope var)])
            (vector-set! depth 0 (cdr info))))
        (nl-let-exp (var val body)
          (translator-s3 scope val)
          (translator-s3 (cons (cons 'nonrec var) scope) body))
        (nl-letrec-exp (var para body exp data)
          (let ([new-scope (cons (cons 'nonrec var) scope)])
            (translator-s3 (var-to-scope (append (list para var) (vector-ref data 0))) body)
            (translator-s3 new-scope exp)
            (vector-set! data 0 (var-to-pos scope (vector-ref data 0)))))
        (nl-proc-exp (para body data)
          (translator-s3 (var-to-scope (cons para (vector-ref data 0))) body)
          (vector-set! data 0 (var-to-pos scope (vector-ref data 0))))
        (nl-call-exp (rator rand)
          (translator-s3 scope rator)
          (translator-s3 scope rand))))))

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
        (nl-var-exp (var depth)
          (apply-env env (vector-ref depth 0)))
        (nl-rec-var-exp (var depth)
          (let ([ret (apply-env env (vector-ref depth 0))])
            (proc-val (procedure (extend-env (car env) ret) (cdr ret)))))         
        (nl-let-exp (var val body)
          (value-of (extend-env env (value-of env val)) body))
        (nl-letrec-exp (var para body exp data)
          (value-of (extend-env env (cons (env-from-pos env (vector-ref data 0)) body)) exp))
        (nl-proc-exp (para body data)
          (proc-val (procedure (env-from-pos env (vector-ref data 0)) body)))
        (nl-call-exp (rator rand)
          ((expval->proc (value-of env rator)) (value-of env rand)))))))

(define run
  (lambda (str)
    (let ([ret (translator-s1 '() (scan&parse str))])
      (translator-s2 ret)
      (translator-s3 '() ret)
      (value-of '() ret))))

(run "let a = 1 in
        let b = 2 in
           let c = 6 in
              letrec double(x) = if zero?(x) then 0 else -((double -(x 1)) -(0 2)) in
                let f = proc(x) (x c) in (f double)")