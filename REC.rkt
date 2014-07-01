#lang eopl

(provide value-of-program)
(provide num-val)
(provide exp-record-entry)
(provide apply-projection)
(provide just-scan)
(provide scan&parse)

; Interpreter for the language REC.
; The program is a solution for the PhD qualification exam on Programming
; Languages from the Fall of 2012 at Stevens Institute of Technology.
; Adriana Compagnoni posed the exam which is available under
; http://www.cs.stevens.edu/~nicolosi/quals/pl-f12.pdf
; This program is based on code from the book "Essentials of Programming Languages"
; by Friedman and Wand, The MIT Press, 3rd edition.
; Test cases are based on the cases from the exam.

;;;************************Environments************************;;;
(define identifier?
  (lambda (sym)
    (if (equal? sym 'lambda) #f #t)))
(define scheme-value? (lambda (v) #t))

(define-datatype environment environment?
  (empty-env)
  (extended-env
   (sym symbol?)
   (val scheme-value?)
   (env environment?)))

(define apply-env
  (lambda (env search-sym)
    (cases environment env
      (empty-env ()
                 (eopl:error 'apply-env "No binding for variable"))
      (extended-env (sym val env)
                    (if (eqv? search-sym sym)
                        val
                        (apply-env env search-sym))))))


;;;************************Let Language************************;;;

;;***datatypes***;;
(define-datatype program program?
  (a-program
   (exp1 expression?)
   (env1 environment?)))

(define-datatype expression expression?
  (const-exp
   (num number?))
  (add-exp
   (exp1 expression?)
   (exp2 expression?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (mult-exp
   (exp1 expression?)
   (exp2 expression?))
  (div-exp
   (exp1 expression?)
   (exp2 expression?))
  (zero?-exp
   (exp1 expression?))
  (if-exp
   (exp1 expression?)
   (exp2 expression?)
   (exp3 expression?))
  (var-exp
   (var identifier?))
  (let-exp
   (var identifier?)
   (exp1 expression?)
   (body expression?))
  (record-exp
   (record-exp-t (list-of record?)))
  (project-exp
   (record expression?)
   (id identifier?)))

(define-datatype record record?
  (record-entry
   (id identifier?)
   (exp expression?)))

;;***Expressed Values***;;
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (record-val
   (record-val-t (list-of exp-record?))))

(define-datatype exp-record exp-record?
  (exp-record-entry
   (id identifier?)
   (expval expval?)))

(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (eopl:error "not an num-val")))))

(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (eopl:error "not an bool-val")))))

(define expval->record
  (lambda (val)
    (cases expval val
      (record-val (records) records)
      (eopl:error "not a record-val"))))

(define init-env (empty-env))

;;***Interpreter***;;
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1 env1)
                 (value-of exp1 env1)))))

;; expression * environment -> expval
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (apply-env env var))
      (add-exp (exp1 exp2)
               (let ((val1 (value-of exp1 env))
                     (val2 (value-of exp2 env)))
                 (let ((num1 (expval->num val1))
                       (num2 (expval->num val2)))
                   (num-val (+ num1 num2)))))
      (diff-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val (- num1 num2)))))
      (mult-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val (* num1 num2)))))
      (div-exp (exp1 exp2)
               (let ((val1 (value-of exp1 env))
                     (val2 (value-of exp2 env)))
                 (let ((num1 (expval->num val1))
                       (num2 (expval->num val2)))
                   (num-val (/ num1 num2)))))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((num1 (expval->num val1)))
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (let-exp (var exp1 body)
               (let ((val1 (value-of exp1 env)))
                 (value-of body
                           (extended-env var val1 env))))
      (record-exp (record)
                (record-val (value-of-list record env)))
      (project-exp (record id)
                (apply-projection (expval->record (value-of record env)) id)))))

;; builds a new record list containing the evaluated expressions of
;;  the given record list
;; (list-of record?) -> (list-of exp-record?)
(define value-of-list
  (lambda (records env)
    (if (null? records) '()
        (let ((rec-value (car records)))
          (cases record rec-value
            (record-entry (id exp)
                          (cons (exp-record-entry id (value-of exp env)) (value-of-list (cdr records) env))))))))

;; (list-of exp-record?) -> expval
(define apply-projection
  (lambda (records identifier)
    (if (null? records)
        (eopl:error "identifier not present in records")
        (let ((entry (car records)))
          (cases exp-record entry
            (exp-record-entry (id expval)
                              (if (equal? id identifier)
                                  expval
                                  (apply-projection (cdr records) identifier))))))))

;;;************************Scanner and Parser************************;;;

;;***Lexical specification***;;
(define the-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    (number (digit (arbno digit)) number)))

;;***Grammar***;;
(define the-grammar
  '(
    (program (expression ";" environment) a-program)
    (environment (identifier number environment) extended-env)
    (environment () empty-env)
    (expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("+" "(" expression "," expression ")") add-exp)
    (expression ("*" "(" expression "," expression ")") mult-exp)
    (expression ("/" "(" expression "," expression ")") div-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("<" (separated-list recordt ",") ">") record-exp)
    (recordt (identifier "=" expression) record-entry)
    (expression ("(" expression "." identifier ")") project-exp)
    ))

(define just-scan
  (sllgen:make-string-scanner the-spec the-grammar))

(define scan&parse
  (sllgen:make-string-parser the-spec the-grammar))
