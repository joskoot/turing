#lang racket

(require "make-Turing-machine.rkt")
(provide test test-report)

(define (test Turing-machine lst expected-state expected-tape)
 (define report? (Turing-report))
 (when report? (printf "~nTest on ~s~n" lst))
 (set! nr-of-tests (add1 nr-of-tests))
 (let/ec ec
  (parameterize
   ((current-error-port (if report? (current-error-port) (open-output-nowhere)))
    (error-escape-handler (λ () (set! nr-of-errors (add1 nr-of-errors)) (ec))))
   (with-handlers ((exn:fail? (λ (exn) (raise exn))))
    (define-values (state tape) (Turing-machine lst))
    (unless (and (equal? state expected-state) (equal? tape expected-tape))
     (when report? (fprintf (current-error-port) "Wrong result~n"))
     (set! nr-of-failures (add1 nr-of-failures)))
    (when report? (printf "Results: state ~s, tape: ~s~n" state tape))))))

(define (test-report)
 (printf "~nTest report~nnr of tests: ~s~n" nr-of-tests)
 (printf "nr-of-failures (errors not included): ~s~n" nr-of-failures)
 (printf "nr-of-errors: ~s~n~n" nr-of-errors)
 (define results (list nr-of-tests nr-of-failures nr-of-errors))
 (set! nr-of-tests 0)
 (set! nr-of-failures 0)
 (set! nr-of-errors 0)
 (apply values results))

(define nr-of-tests 0)
(define nr-of-failures 0)
(define nr-of-errors 0)
