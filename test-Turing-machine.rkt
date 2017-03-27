#lang racket

(require "make-Turing-machine.rkt" "tester.rkt")

;===================================================================================================
;
; The following Turing machine terminates for every list of symbols x and +.
; A correct input is (x ... [+ x ...]).
; The result of a correct input is the input without +.
; This is like adding two natural numbers.
; Without + the tm returns the input.
; When encountering a + it is replaced by x and at the end one x will be erased.
; With a correct input the machine halts in state T.
; With erroneous input containing no other tape-symbols than x and + the machine halts in state F.
; An input containing any other tape-symbol than x or + causes an error to be raised.

(define Turing-machine
 (make-Turing-machine '0 '(T F) 'B 'b '_ ; T/F final state for accepted/rejected input.
  ; state 0 : before encountering + or end of tape.
  ; state 1 : after encountering an x.
  ; state 2 : erase x that originally was +.
  ; state 3 : rewinding the tape before finishing.
 '(((0 x) (0 x R))    ; Accept the x and process the remainder.
   ((0 +) (1 x R))    ; Replace + by x. At the end one x will be erased.
   ((0 B) (3 b L))    ; The input has no + and is accepted. Go rewind the tape.
   ((1 x) (1 x R))    ; Accept the x and process the remainder.
   ((1 +) (F + L))    ; Do not accept a second +.
   ((1 B) (2 b L))    ; Go erase an x in order to account for the x produced by +.
   ((2 x) (3 b L))    ; Erase x and go rewind the tape. Not necessary; just fun.
   ((3 x) (3 x L))    ; Keep on rewinding.
   ((3 B) (T b R))))) ; Accept the input.

(Turing-report #t)

(test Turing-machine '()                  'T '())
(test Turing-machine '(x x x + x x)       'T '(x x x x x))
(test Turing-machine '(x x x +)           'T '(x x x))
(test Turing-machine '(+ x x)             'T '(x x))
(test Turing-machine '(+)                 'T '())
(test Turing-machine '(x x x x x)         'T '(x x x x x))
(test Turing-machine '(x)                 'T '(x))
(test Turing-machine '()                  'T '())
(test Turing-machine '(+ +)               'F '(x +))
(test Turing-machine '(+ x +)             'F '(x x +))
(test Turing-machine '(x x + x + x)       'F '(x x x x + x))

(define-values (a b c) (test-report))

(test Turing-machine '(B) 'T '())
(test Turing-machine '(b) 'T '())
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
