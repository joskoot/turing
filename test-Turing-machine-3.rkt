#lang racket

(require "make-Turing-machine.rkt" "tester.rkt")

;===================================================================================================

(define rules
'(((0 B) (T _ N))
  ((0 y) (F _ N))
  ((0 _) (0 _ R))))

(define Turing-machine (make-Turing-machine '0 '(T F) 'B 'b '_ rules))

(Turing-report? #t)

(test Turing-machine '()                'T '())
(test Turing-machine '(x x x + x x)     'T '(x x x + x x))
(test Turing-machine '(x x y x x)       'F '(x x y x x))

(test-report)

;===================================================================================================
