#lang racket

(require "make-turing-machine.rkt")
(provide test-turing-machine)

;===================================================================================================
;
; The following Turing machine terminates for every list of symbols x and +.
; A correct input is (x ... [+ x ...] ...).
; The result of a correct input is the input without +.
; This is like addition of zero, one or more natural numbers.
; With a correct input the machine halts in state T.
; An input containing any other tape-symbol than x or + or b causes an error to be raised.
; Given an input containing b, the machine halts in state F.

(define (test-turing-machine report?)
 
 (define turing-machine
  (make-turing-machine '0 '(T F) report? 'B 'b
  '(((0 x) (0 x R))    ; Ok, continue checking.
    ((0 +) (0 + R))    ; Ok, continue checking.
    ((0 b) (F b L))    ; Wrong.
    ((0 B) (1 b L))    ; End of tape reached. Go rewind the tape.
    ((1 x) (1 x L))    ; Rewibnd the tape.
    ((1 +) (1 + L))
    ((1 B) (2 b R))    ; Start of tape reached. Find the first x.
    ((2 x) (3 x R))    ; Start the addition.
    ((2 +) (2 b R))    ; Ignore heading +.
    ((2 b) (T b L))    ; No x or + present. Result (b).
    ((2 B) (T b L))    ; No x or + present. Result (b).
    ((3 x) (3 x R))    ; Accept x.
    ((3 +) (4 x L))    ; Replace + by x and go remove the first x.
    ((3 B) (T b L))    ; Done.
    ((3 b) (T b L))    ; Done.
    ((4 x) (4 x L))    ; Go to start of tape.
    ((4 b) (5 b R))    ; Start encountered. Go remove first x.
    ((4 B) (5 b R))    ; Start encountered. Go remove first x.
    ((5 x) (3 b R))))) ; Remove first x and continue addition.
 
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
 (test '(+ +)               'T '())
 (test '(+ x +)             'T '(x))
 (test '(x x + x + x)       'T '(x x x x))
 (test '(x + x x + x x x)   'T '(x x x x x x))
 (test '(x x b x x)         'F '(x x b x x))
 
 (define all-ok (and (zero? nr-of-failures) (zero? nr-of-errors)))
 
 (test-report)
 
 (when report? (eprintf "The following errors are expected.~n"))
 
 (test '(B) 'T '())
 (test '(z) 'F '())
 (test '(y x x z x x ) 'F '())
 (test '(y + x z x) 'F '())
 
 (when report?
  (printf  "~nThe following test report should show no failures,~n")
  (eprintf "but must show as many errors as tests.~n"))
 
 (define all:ok (and all-ok (zero? nr-of-failures) (= nr-of-tests nr-of-errors)))
 
 (test-report)
 
 (when report? (eprintf "Check below that all is well.~n"))
 
 (if all:ok (printf "All is well.~n") (error "One or more tests failed.")))

;===================================================================================================

(test-turing-machine #f)