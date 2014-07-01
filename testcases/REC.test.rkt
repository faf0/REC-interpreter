#lang eopl

(require "../REC.rkt")

;;***Test Cases***;;
; These test cases are based on the test cases from:
; http://www.cs.stevens.edu/~nicolosi/quals/pl-f12.pdf

(just-scan "if zero? (5) then 1 else 3;")
(scan&parse "if zero? (5) then 1 else 3;")

(scan&parse "3 ; x 5 y 7")
(scan&parse "let z = 5 in let x = 3 in let y = -(x, 1) in let x = 4 in -(z, -(x,y)); c2 666")

(value-of-program (scan&parse "<a=2, b=3, f=3>; y 55"))
(value-of-program (scan&parse "<a=2, b=-(3,44), f=3>;"))

(define fortyfourproj (apply-projection (list (exp-record-entry 'x (num-val 33)) (exp-record-entry 'y (num-val 44))) 'y))
(define twelveproj (value-of-program (scan&parse "(<x = 12, y = 1>.x);")))
(define threeproj (value-of-program (scan&parse "(<a=2, b=-(3,44), f=3>.f); y 55")))
(define threecomplex (value-of-program (scan&parse "let a=5 in (<x = 7, y = <z = 1, w = 75>, f = -(a,2)>.f);")))

; check the result of every test case in the list
(define test-run
  (lambda (l i)
    (if (null? l) "Tests completed successfully!"
        (if (not (car l))
            (string-append "Test case "  (number->string i) " failed!")
            (test-run (cdr l) (+ i 1))))))

; all test cases in a list
(define tests
  (list
   (equal? fortyfourproj (num-val 44))
   (equal? twelveproj (num-val 12))
   (equal? threeproj (num-val 3))
   (equal? threecomplex (num-val 3))
   ))

; show the test results
(display (test-run tests 1))
