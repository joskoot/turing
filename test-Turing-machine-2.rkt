#lang racket

(require "make-Turing-machine.rkt" "tester.rkt")

;===================================================================================================
;
; The following Turing machine always terminates.
; A correct input is @nonbreaking{@tt["(x ... [+ x ...] ...)"]}.
; The result of a correct input is the input without @tt["+"].
; This is like addition of zero, one or more natural numbers.
; With a correct input the machine halts in state @tt["T"].
; With incorrect input the machine halts in state @tt["F"].
; @tt["B"] is the machine-blank, @tt["b"] the user-blank and @tt["_"] the dummy-symbol.

(define rules
'(;State 0 : Inspect the very first element.")
  ;          Mark start x with y or start + with p.")
  ;          This way we can avoid moving left")
  ;          of the start of the input.")
  ((0 x) (1 y R))  ;Ok, continue checking the input.")
  ((0 +) (1 p R))  ;Ok, continue checking the input.")
  ((0 B) (T b N))  ;Empty input accepted.")
  ((0 _) (F _ N))  ;Reject incorrect input.")
  ;State 1 : Check the remainder of the input.")
  ((1 x) (1 x R))  ;Ok, continue the check.")
  ((1 +) (1 + R))  ;Ok, continue the check.")
  ((1 B) (2 b L))  ;Input is ok. Start the addition.")
  ((1 _) (F _ N))  ;Reject incorrect input.")
  ;State 2 : Do the addition from left to right.")
  ((2 x) (2 x L))  ;Leave x as it is and continue addition.")
  ((2 y) (T x N))  ;Start of input reached. Done.")
  ((2 +) (3 x R))  ;Replace + by x and go erase the last x.")
  ((2 p) (3 y R))  ;Replace p by y and go erase the last x.")
  ;State 3 : Go to end of tape.")
  ((3 x) (3 x R))  ;Keep looking for end of input.")
  ((3 b) (4 b L))  ;End of input reached. Go erase one x.")
  ;State 4 : Erase the last x.")
  ((4 x) (2 b L))  ;Erase x and continue addition.")
  ((4 y) (T b N))  ;Erase y (which was an x) and accept.")
  ))

(define Turing-machine (make-Turing-machine '0 '(T F) 'B 'b '_ rules))

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
(test Turing-machine '(x x b x x)       'F '(y x b x x))

(define-values (a b c) (test-report))

(test Turing-machine '(z) 'F '(z))
(test Turing-machine '(z x x z x x) 'F '(z x x z x x))
(test Turing-machine '(y + x z x) 'F '(y + x z x))

(define-values (d e f) (test-report))

(if (= 0 b c e f)
 (printf "All is well.~n")
 (error "One or more tests failed."))

