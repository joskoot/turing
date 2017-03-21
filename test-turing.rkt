#lang racket

(require "turing.rkt")

;===================================================================================================
;
; The following tm terminates for every list of symbols x and +.
; A correct input is (x ... [+ x ...]).
; Tape-symbol y is treated as tape-symbol x (included only for testing the report)
; The result of a correct input is the input without +.
; This is like adding two natural numbers.
; Without + the tm returns the input.
; When encountering a + it is replaced by x and at the end one x will be erased.
; A correct input halts with state T.
; An erroneous input containing no other tape-symbols than x and + halts in state F.
; An input containing any other tape-symbol than x or + causes an error to be raised.

(define (test report?)
 
 (define tm
  (make-tm '0 '(T F) report? 'B 'b ; T/F final state for accepted/rejected input.
  '((0               ; Initial state. No + encountered yet.
     (x (0 x R))            
     (y (0 y R))            
     (+ (1 x R))            ; Replace + by x. At end one x will be erased.
     (B (3 b L)))           ; The input has no + and is accepted. Go rewind the tape.
    (1               ; A + has been encountered.
     (x (1 x R)) 
     (y (1 y R)) 
     (+ (F + L))            ; After + do not accept a second +.
     (B (2 b L)))           ; Go erase an x in order to account for the x produced by +.
    (2               ; Erase one x. In this state the current tape-symbol always is x.
     (x (3 b L))            ; Go rewind the tape.
     (y (3 b L)))           ; Go rewind the tape.
    (3               ; Rewind the tape (just for pleasure)
     (x (3 x L))            ; Keep on rewinding.
     (y (3 y L))            ; Keep on rewinding.
     (B (T b R))))))        ; Accept the input.
 
 (define (test lst expected-state expected-tape)
  (when report? (printf "~nTest on ~s~n" lst))
  (set! nr-of-tests (add1 nr-of-tests))
  (let/ec ec
   (parameterize
    ((current-error-port (if report? (current-error-port) (open-output-nowhere)))
     (error-escape-handler
      (λ () (set! nr-of-errors (add1 nr-of-errors)) (ec))))
    (with-handlers ((exn:fail? (λ (exn) (raise exn))))
     (define-values (state tape) (tm lst))
     (unless (and (equal? state expected-state) (equal? tape expected-tape))
      (when report? (fprintf (current-error-port) "Wrong result~n"))
      (set! nr-of-failures (add1 nr-of-failures)))
     (when report? (printf "Results: state ~s, tape: ~s~n" state tape))))))
 
 (define (test-report)
  (when report?
   (printf "~nTest report~nnr of tests: ~s~n" nr-of-tests)
   (printf "nr-of-failures (errors not included): ~s~n" nr-of-failures)
   (printf "nr-of-errors: ~s~n~n" nr-of-errors))
  (set! nr-of-tests 0)
  (set! nr-of-failures 0))
 
 (define nr-of-tests 0)
 (define nr-of-failures 0)
 (define nr-of-errors 0)
 
 (when report? (eprintf "~nCheck at the end of all output that all is well.~n"))

 (test '()                  'T '())
 (test '(x x x + x x)       'T '(x x x x x))
 (test '(x x x +)           'T '(x x x))
 (test '(+ x x)             'T '(x x))
 (test '(+)                 'T '())
 (test '(x x x x x)         'T '(x x x x x))
 (test '(x)                 'T '(x))
 (test '()                  'T '())
 (test '(+ +)               'F '(x +))
 (test '(+ x +)             'F '(x x +))
 (test '(x x + x + x)       'F '(x x x x + x))
 (test '(x y y x + x y x y) 'T '(x y y x x x y x))
 
 (define all-ok (and (zero? nr-of-failures) (zero? nr-of-errors)))
 
 (test-report)
 
 (when report? (eprintf "The following errors are expected.~n"))
 
 (test '(B) 'T '())
 (test '(b) 'T '())
 (test '(z) 'F '())
 (test '(y x x z x x ) 'F '())
 (test '(y + x z x) 'F '())
 
 (when report?
  (printf "~nThe following test report should show no failures,~n~
             but must show as many errors as tests.~n"))
 
 (define all:ok (and all-ok (zero? nr-of-failures) (= nr-of-tests nr-of-errors)))
 
 (test-report)
 
 (when report? (eprintf "Check below that all is well.~n"))
 
 (if all:ok (printf "All is well.~n") (error "One or more tests failed.")))

;===================================================================================================

(test #f)

;===================================================================================================
