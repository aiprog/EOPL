; ToyLan: A Toy Language
#lang racket

(require eopl)

(define-datatype environment environment?
  (empty-env)
  (ext-env (env environment?) (var symbol?) (val (lambda (t) #t)))
  (ext-env-rec (env environment?) (names (list-of symbol?)) (params (list-of symbol?)) (bodies (list-of statement?)) (closures vector?)))

(define (location lst var)
  (cond
    [(null? lst) #f]
    [(eqv? (car lst) var) 0]
    [else (let ([pos (location (cdr lst) var)])
            (if pos (add1 pos) #f))]))
          
(define (apply-env env var)
  (cases environment env
    (empty-env ()
      (eopl:error 'apply-env "No binding for ~s" var))
    (ext-env (saved-env saved-var val)
      (if (eqv? saved-var var)
          val
          (apply-env saved-env var)))
    (ext-env-rec (saved-env names params bodies closures)
      (let ([pos (location names var)])
        (if pos
            (let ([ref (vector-ref closures pos)])
              (if (not ref)
                  (vector-set! closures pos (newref (proc-val (procedure env (list-ref params pos) (list-ref bodies pos)))))
                  (void))
              (vector-ref closures pos))
            (apply-env saved-env var))))))

(define scanner-spec
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number ((or (concat digit (arbno digit)) (concat "-" digit (arbno digit)))) number)))

(define parser-spec
  '((program ((arbno statement)) stmt-prog)
    (statement ("read" identifier) read-stmt)
    (statement ("print" expression) print-stmt)
    (statement ("var" (arbno identifier "=" expression) ";") var-stmt)
    (statement ("func" (arbno identifier "(" identifier ")" statement) ";") func-stmt)
    (statement (identifier "=" expression) assign-stmt)
    (statement ("if" expression "then" statement "else" statement) if-stmt)
    (statement ("while" expression statement) while-stmt)
    (statement ("break") break-stmt)
    (statement ("return" expression) ret-stmt)
    (statement ("{" (arbno statement) "}") blk-stmt)
    (statement ("try" statement "catch" "(" identifier ")" statement) try-stmt)
    (statement ("raise" expression) raise-stmt)
    (expression (number) const-exp)
    (expression ("-" "(" expression expression ")") diff-exp)
    (expression ("not" "(" expression ")") not-exp)
    (expression ("zero?" "(" expression ")") zero-exp)
    (expression (identifier) var-exp)
    (expression ("proc" "(" identifier ")" statement) proc-exp)
    (expression ("(" expression expression ")") call-exp)))

(sllgen:make-define-datatypes scanner-spec parser-spec)

(define scan&parse
  (sllgen:make-string-parser scanner-spec parser-spec))

(define-datatype expval expval?
  (void-val)
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc procedure?)))

(define (expval->num val)
  (cases expval val
    (num-val (num) num)
    (else (eopl:error 'expval->num "Bad conversion: ~s" val))))

(define (expval->bool val)
  (cases expval val
    (bool-val (bool) bool)
    (else (eopl:error 'expval->bool "Bad conversion: ~s" val))))

(define (expval->proc val)
  (cases expval val
    (proc-val (proc) proc)
    (else (eopl:error 'expval->proc "Bad conversion: ~s" val))))

(define (procedure env param body)
  (lambda (cont arg)
    (value-of-stmt cont (ext-env env param (newref arg)) body)))

(define the-store '())

(define (newref val)
  (let ([ref (length the-store)])
    (set! the-store (append the-store (list val)))
    ref))

(define (deref ref)
  (list-ref the-store ref))

(define (setref! ref val)
  (set! the-store
        (letrec ([setref-inner
                  (lambda (store ref1 val1)
                    (if (zero? ref1)
                        (cons val (cdr store))
                        (cons (car store) (setref-inner (cdr store) (sub1 ref1) val))))])
          (setref-inner the-store ref val))))

(define-datatype continuation continuation?
  (empty-cont)
  (stmt-cont (cont continuation?) (env environment?) (stmts (list-of statement?)))
  (print-cont (cont continuation?))
  (var-cont (cont continuation?) (env environment?) (var symbol?) (vars (list-of symbol?)) (exps (list-of expression?)))
  (assign-cont (cont continuation?) (env environment?) (var symbol?))
  (if-cont (cont continuation?) (env environment?) (then statement?) (else statement?))
  (then-else-cont (cont continuation?))
  (while-exp-cont (cont continuation?) (env environment?) (exp expression?) (stmt statement?))
  (while-stmt-cont (cont continuation?) (env environment?) (exp expression?) (stmt statement?))
  (ret-cont (cont continuation?))
  (diff-cont1 (cont continuation?) (env environment?) (exp2 expression?))
  (diff-cont2 (cont continuation?) (val1 expval?))
  (not-cont (cont continuation?))
  (zero-cont (cont continuation?))
  (call-cont1 (cont continuation?) (env environment?) (rand expression?))
  (call-cont2 (cont continuation?) (rator expval?))
  (call-cont3 (cont continuation?))
  (try-cont (cont continuation?) (env environment?) (var symbol?) (handler statement?))
  (raise-cont (cont continuation?))
  )

(define (prev-cont cont)
  (cases continuation cont
    (empty-cont () (eopl:error 'prev-cont "An empty continuation"))
    (stmt-cont (cont env stmts) cont)
    (print-cont (cont) cont)
    (var-cont (cont env var vars exps) cont)
    (assign-cont (cont env var) cont)
    (if-cont (cont env then else) cont)
    (then-else-cont (cont) cont)
    (while-exp-cont (cont env exp stmt) cont)
    (while-stmt-cont (cont env exp stmt) cont)
    (ret-cont (cont) cont)
    (diff-cont1 (cont env exp2) cont)
    (diff-cont2 (cont val1) cont)
    (not-cont (cont) cont)
    (zero-cont (cont) cont)
    (call-cont1 (cont env rand) cont)
    (call-cont2 (cont rator) cont)
    (call-cont3 (cont) cont)
    (try-cont (cont env var handler) cont)
    (raise-cont (cont) cont)))

(define (find-loop-cont cont)
  (cases continuation cont
    (empty-cont () (eopl:error 'find-loop-cont "An empty continuation"))
    (call-cont3 (cont) (eopl:error 'find-loop-cont "A call continuation"))
    (while-stmt-cont (cont env exp stmt) cont)
    (else (find-loop-cont (prev-cont cont)))))

(define (find-call-cont3 cont)
  (cases continuation cont
    (empty-cont () (eopl:error 'find-call-cont "An empty continuation"))
    (call-cont3 (cont) cont)
    (else (find-call-cont3 (prev-cont cont)))))

(define (find-try-cont cont)
  (cases continuation cont
    (empty-cont () (eopl:error 'find-try-cont "An empty continuation"))
    (try-cont (cont1 env var handler) cont)
    (else (find-try-cont (prev-cont cont)))))

(define (apply-cont cont val)
  (cases continuation cont
    (empty-cont ()
      (void))
    (stmt-cont (cont env stmts)
      (if (null? stmts)
        (apply-cont cont (void-val))
        (let ([new-env env])
          (if (expval? val)
              (void)
              (set! new-env val))
          (value-of-stmt (stmt-cont cont new-env (cdr stmts)) new-env (car stmts)))))
    (print-cont (cont)
      (begin
        (display val)
        (newline)
        (apply-cont cont (void-val))))
    (var-cont (cont env var vars exps)
      (let* ([ref (newref val)]
             [new-env (ext-env env var ref)])
        (if (null? vars)
            (apply-cont cont new-env)
            (value-of-exp (var-cont cont new-env (car vars) (cdr vars) (cdr exps)) new-env (car exps)))))
    (assign-cont (cont env var)
      (begin
        (setref! (apply-env env var) val)
        (apply-cont cont (void-val))))
    (if-cont (cont env then else)
      (if (expval->bool val)
          (value-of-stmt (then-else-cont cont) env then)
          (value-of-stmt (then-else-cont cont) env else)))
    (then-else-cont (cont)
      (apply-cont cont (void-val)))
    (while-exp-cont (cont env exp stmt)
      (if (expval->bool val)
          (value-of-stmt (while-stmt-cont cont env exp stmt) env stmt)
          (apply-cont cont (void-val))))
    (while-stmt-cont (cont env exp stmt)
      (value-of-exp (while-exp-cont cont env exp stmt) env exp))
    (ret-cont (cont)
      (apply-cont (find-call-cont3 cont) val))
    (try-cont (cont env var handler)
      (apply-cont cont val))
    (raise-cont (cont)
      (cases continuation (find-try-cont cont)
        (try-cont (cont env var handler)
          (value-of-stmt cont (ext-env env var (newref val)) handler))
        (else (void))))
    (diff-cont1 (cont env exp2)
      (value-of-exp (diff-cont2 cont val) env exp2))
    (diff-cont2 (cont val1)
      (apply-cont cont (num-val (- (expval->num val1) (expval->num val)))))
    (not-cont (cont)
      (apply-cont cont (bool-val (not (expval->bool val)))))
    (zero-cont (cont)
      (if (zero? (expval->num val))
          (apply-cont cont (bool-val #t))
          (apply-cont cont (bool-val #f))))
    (call-cont1 (cont env rand)
      (value-of-exp (call-cont2 cont val) env rand))
    (call-cont2 (cont rator)
      ((expval->proc rator) (call-cont3 cont) val))
    (call-cont3 (cont)
      (apply-cont cont val))))

(define (value-of-exp cont env exp)
  (cases expression exp
    (const-exp (num)
      (apply-cont cont (num-val num)))
    (diff-exp (exp1 exp2)
      (value-of-exp (diff-cont1 cont env exp2) env exp1))
    (not-exp (exp)
      (value-of-exp (not-cont cont) env exp))
    (zero-exp (exp)
      (value-of-exp (zero-cont cont) env exp))
    (var-exp (var)
      (apply-cont cont (deref (apply-env env var))))
    (proc-exp (param body)
      (apply-cont cont (proc-val (procedure env param body))))
    (call-exp (rator rand)
      (value-of-exp (call-cont1 cont env rand) env rator))))  
    
(define (value-of-stmt cont env stmt)
  (cases statement stmt
    (read-stmt (var)
      (begin
        (setref! (apply-env env var) (read))
        (apply-cont (void-val))))
    (print-stmt (exp)
      (value-of-exp (print-cont cont) env exp))
    (var-stmt (vars exps)
      (value-of-exp (var-cont cont env (car vars) (cdr vars) (cdr exps)) env (car exps)))
    (func-stmt (names params bodies)
      (apply-cont cont (ext-env-rec env names params bodies (make-vector (length names) #f))))
    (assign-stmt (var exp)
      (value-of-exp (assign-cont cont env var) env exp))
    (if-stmt (if then else)
      (value-of-exp (if-cont cont env then else) env if))
    (while-stmt (exp stmt)
      (value-of-exp (while-exp-cont cont env exp stmt) env exp))
    (break-stmt ()
      (apply-cont (find-loop-cont cont) (void-val)))
    (ret-stmt (exp)
      (value-of-exp (ret-cont cont) env exp))
    (blk-stmt (stmts)
      (value-of-stmt (stmt-cont cont env (cdr stmts)) env (car stmts)))
    (try-stmt (stmt var handler)
      (value-of-stmt (try-cont cont env var handler) env stmt))
    (raise-stmt (exp)
      (value-of-exp (raise-cont cont) env exp))))
  
(define (value-of-prog cont env prog)
  (cases program prog
    (stmt-prog (stmts)
      (value-of-stmt (stmt-cont cont env (cdr stmts)) env (car stmts)))))

(define run
  (lambda (program)
    (value-of-prog (empty-cont) (empty-env) (scan&parse program))))

(run "var num = 20;
      func sum(x)
      {
        var tmp = 0;
        while not(zero?(x))
        {
          if zero?(-(x 10))
          then raise 999999
          else tmp = -(tmp -(0 x))
          x = -(x 1)
        }

        return tmp
      };
      try
        print (sum num)
      catch (i)
        print i")

















