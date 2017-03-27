#lang racket

(require "make-Turing-machine.rkt" "tester.rkt")

;===================================================================================================

(define rules
'(((0 b) (F _ N))
  ((0 B) (T _ N))
  ((0 _) (0 _ R))))

(define Turing-machine (make-Turing-machine '0 '(T F) 'B 'b '_ rules))

(Turing-report? #t)

(test Turing-machine '()                'T '())
(test Turing-machine '(p q r s t)       'T '(p q r s t))
(test Turing-machine '(x x b x x)       'F '(x x b x x))
(test Turing-machine '(_)               'F '())

(call-with-values test-report
 (λ (a b c)
  (if (and (zero? b) (= c 1))
   (printf "All is well, test report as expected.~n")
   (error "Test report not as expected"))))

;===================================================================================================
