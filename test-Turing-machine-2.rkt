#lang racket

(require "make-Turing-machine.rkt" "tester.rkt")

;===================================================================================================
;
; The following Turing machine terminates for every list of symbols x and +.
; A correct input is (x ... [+ x ...] ...).
; The result of a correct input is the input without +.
; This is like addition of zero, one or more natural numbers.
; With a correct input the machine halts in state T.
; An input containing any other tape-symbol than x or + or b causes an error to be raised.
; Given an input containing b, the machine halts in state F.

(define rules
 ; state 0 : Check that the input does not contain b.
 ; state 1 : Rewind the tape.
 ; state 2 : Find leftmost x.
 ; state 3 : Do the addition
 ; state 4 : Rewind the tape.
 ; state 5 : Remove left-most x and continue the addition.
'(((0 x) (0 x R))    ; Ok, continue checking that the input contains no b.
  ((0 +) (0 + R))    ; Ok, continue checking that the input contains no b.
  ((0 b) (F b R))    ; Wrong, the input must not contain b.
  ((0 B) (1 b L))    ; End of tape reached. Go rewind the tape.
  ((1 x) (1 x L))    ; Keep on rewinding.
  ((1 +) (1 + L))    ; Keep on rewinding
  ((1 B) (2 b R))    ; Start of tape reached. Find the first x.
  ((2 x) (3 x R))    ; Start the addition.
  ((2 +) (2 b R))    ; Ignore heading +.
  ((2 b) (T b L))    ; No x or + present. Result (b).
  ((2 B) (T b L))    ; No x or + present. Result (b).
  ((3 x) (3 x R))    ; Accept x.
  ((3 +) (4 x L))    ; Replace + by x and go remove the first x.
  ((3 B) (T b R))    ; Done.
  ((3 b) (T b R))    ; Done.
  ((4 x) (4 x L))    ; Go to start of tape.
  ((4 b) (5 b R))    ; Start encountered. Go remove first x.
  ((4 B) (5 b R))    ; Start encountered. Go remove first x.
  ((5 x) (3 b R))))  ; Remove first x and continue addition.

(define Turing-machine (make-Turing-machine '0 '(T F) 'B 'b '_ rules))

(Turing-report? #t)

(test Turing-machine '()                'T '())
(test Turing-machine '(x x x + x x)     'T '(x x x x x))
(test Turing-machine '(x x x +)         'T '(x x x))
(test Turing-machine '(+ x x)           'T '(x x))
(test Turing-machine '(+)               'T '())
(test Turing-machine '(x x x x x)       'T '(x x x x x))
(test Turing-machine '(x)               'T '(x))
(test Turing-machine '()                'T '())
(test Turing-machine '(+ +)             'T '())
(test Turing-machine '(+ x +)           'T '(x))
(test Turing-machine '(x x + x + x)     'T '(x x x x))
(test Turing-machine '(x + x x + x x x) 'T '(x x x x x x))
(test Turing-machine '(x x b x x)       'F '(x x b x x))

(define-values (a b c) (test-report))

(test Turing-machine '(B) 'T '())
(test Turing-machine '(z) 'F '())
(test Turing-machine '(y x x z x x ) 'F '())
(test Turing-machine '(y + x z x) 'F '())


(define-values (d e f) (test-report))

(if
 (and
  (= b 0)
  (= c 0)
  (= d f))
 (printf "All is well.~n")
 (error "One or more tests failed."))

;===================================================================================================
