#lang racket

(require "make-turing-machine.rkt")
(provide test-turing-machine)

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

(define (test-turing-machine report?)
 
 (define turing-machine
  (make-turing-machine '0 '(T F) report? 'B 'b ; T/F final state for accepted/rejected input.
  '(((0 x) (0 x R))        ; Accept the x and process the remainder.
    ((0 +) (1 x R))        ; Replace + by x. At the end one x will be erased.
    ((0 B) (3 b L))        ; The input has no + and is accepted. Go rewind the tape.
    ((1 x) (1 x R))        ; Accept the x and process the remainder.
    ((1 +) (F + L))        ; After + do not accept a second +.
    ((1 B) (2 b L))        ; Go erase an x in order to account for the x produced by +.
    ((2 x) (3 b L))        ; Go rewind the tape.
    ((3 x) (3 x L))        ; Keep on rewinding.
    ((3 B) (T b R)))))     ; Accept the input.
 
 (define (test lst expected-state expected-tape)
  (when report? (printf "~nTest on ~s~n" lst))
  (set! nr-of-tests (add1 nr-of-tests))
  (let/ec ec
   (parameterize
    ((current-error-port (if report? (current-error-port) (open-output-nowhere)))
     (error-escape-handler (λ () (set! nr-of-errors (add1 nr-of-errors)) (ec))))
    (with-handlers ((exn:fail? (λ (exn) (raise exn))))
     (define-values (state tape) (turing-machine lst))
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
 
 (when report? (eprintf "~nCheck at the end of all output that ")
                (printf "all is well.~n"))

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
 
 (define all-ok (and (zero? nr-of-failures) (zero? nr-of-errors)))
 
 (test-report)
 
 (when report? (eprintf "The following errors are expected.~n"))
 
 (test '(B) 'T '())
 (test '(b) 'T '())
 (test '(z) 'F '())
 (test '(y x x z x x ) 'F '())
 (test '(y + x z x) 'F '())
 
 (when report?
  (printf  "~nThe following test report should show no failures,~n")
  (eprintf "but must show as many errors as tests.~n"))
 
 (define all:ok (and all-ok (zero? nr-of-failures) (= nr-of-tests nr-of-errors)))
 
 (test-report)
 
 (when report? (eprintf "Check below that ") (printf "all is well.~n"))
 
 (if all:ok (printf "All is well.~n") (error "One or more tests failed.")))

;===================================================================================================
