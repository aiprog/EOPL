; IMPLICIT-REFS-STMT: A Language with Implicit References (with Statements)
#lang racket

(require (lib "eopl.ss" "eopl"))

(define-datatype environment environment?
  (empty-env)
  (extend-env (pre environment?) (var symbol?) (val (lambda (t) #t)))
  (extend-env-rec (pre environment?) (name (list-of symbol?)) (para (list-of symbol?)) (body (list-of statement?)) (closure vector?)))

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
      (extend-env-rec (pre var para body closure)
        (let ([pos (location var search-var)])
          (if pos
            (let ([ref (vector-ref closure pos)])
              (if (not ref)
                (vector-set! closure pos (newref (proc-val (procedure env (list-ref para pos) (list-ref body pos)))))
                #f)
              (vector-ref closure pos))
            (apply-env pre search-var)))))))

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
    (statement ("var" (arbno identifier "=" expression) ";" (arbno identifier "(" identifier ")" "=" statement) ";" statement) var-stmt)
    (statement ("read" identifier) read-stmt)
    (statement ("return" expression) ret-stmt)
    (expression (number) const-exp)
    (expression ("+" "(" expression expression ")") add-exp)
    (expression ("-" "(" expression expression ")") diff-exp)
    (expression ("not" "(" expression ")") not-exp)
    (expression ("zero?" "(" expression ")") zero-exp)
    (expression (identifier) var-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)))

(sllgen:make-define-datatypes scanner-spec parser-spec)

(define scan&parse
  (sllgen:make-string-parser scanner-spec parser-spec))

(define procedure
  (lambda (env para body)
    (lambda (val)
      (value-of-stmt (extend-env env para (newref val)) body))))

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc procedure?)))

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

(define value-of-pgm
  (lambda (env pgm)
    (cases program pgm
      (a-program (stmt)
        (value-of-stmt env stmt)))))

(define value-of-block-stmt
  (lambda (env block)
    (if (not (null? block))
      (let* ([first (car block)]
             [val (value-of-stmt env first)]
             [remain (cdr block)])
        (if (void? val)
          (value-of-block-stmt env remain)
          val))
      (void))))

(define value-of-while-stmt
  (lambda (env exp stmt)
    (let ([val (expval->bool (value-of-exp env exp))])
      (if val
        (begin
          (let ([val (value-of-stmt env stmt)])
            (if (void? val)
              (value-of-while-stmt env exp stmt)
              val)))
        (void)))))

(define extend-env-by-var-list
  (lambda (env var exp)
    (if (not (null? var))
      (let ([first-var (car var)]
            [first-val (value-of-exp env (car exp))])
        (extend-env-by-var-list (extend-env env first-var (newref first-val)) (cdr var) (cdr exp)))
      env))) 

(define value-of-stmt
  (lambda (env stmt)
    (cases statement stmt
      (assign-stmt (var exp)
        (setref! (apply-env env var) (value-of-exp env exp)))
      (print-stmt (exp)
        (print (value-of-exp env exp))
        (newline))
      (block-stmt (block)
        (value-of-block-stmt env block))
      (if-stmt (exp stmt-then stmt-else)
        (let ([val (expval->bool (value-of-exp env exp))])
          (if val
            (value-of-stmt env stmt-then)
            (value-of-stmt env stmt-else))))
      (while-stmt (exp stmt)
        (value-of-while-stmt env exp stmt))
      (var-stmt (var exp proc para body stmt)
        (let ([new-env (extend-env-by-var-list env var exp)])
          (value-of-stmt (extend-env-rec new-env proc para body (make-vector (length proc) #f)) stmt)))
      (read-stmt (var)
        (setref! (apply-env env var) (num-val (read))))
      (ret-stmt (exp)
        (value-of-exp env exp)))))
        
(define value-of-exp
  (lambda (env exp)
    (cases expression exp
      (const-exp (number)
        (num-val number))
      (add-exp (exp-a exp-b)
        (let ([val-a (expval->num (value-of-exp env exp-a))]
              [val-b (expval->num (value-of-exp env exp-b))])
          (num-val (+ val-a val-b))))
      (diff-exp (exp-a exp-b)
        (let ([val-a (expval->num (value-of-exp env exp-a))]
              [val-b (expval->num (value-of-exp env exp-b))])
          (num-val (- val-a val-b))))
      (not-exp (exp)
        (let ([val (expval->bool (value-of-exp env exp))])
          (bool-val (not val))))
      (zero-exp (exp)
        (let ([val (expval->num (value-of-exp env exp))])
          (if (zero? val)
            (bool-val #t)
            (bool-val false))))
      (var-exp (var)
         (deref (apply-env env var)))
      (proc-exp (para body)
        (proc-val (procedure env para body)))
      (call-exp (exp arg)
        (let ([val-a (expval->proc (value-of-exp env exp))]
              [val-b (value-of-exp env arg)])
          (val-a val-b))))))

(define run
  (lambda (program)
    (value-of-pgm (empty-env) (scan&parse program))))

(initialize-store!)

(run "var x = 10 y = 0;
          sum(x) = 
          {
            while not(zero?(x))
            {
              if zero?(-(x 8))
              then return y
              else
              {
                y = +(y x);
                x = -(x 1);
              };
            };

            return y;
          };
          print (sum x)")