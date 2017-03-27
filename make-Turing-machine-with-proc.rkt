#lang racket

(provide make-Turing-machine)

#|==================================================================================================

Module make-Turing-machine.scrbl produces documentation.

==================================================================================================|#

(define (make-Turing-machine starting-state final-states report? machine-blank user-blank rules)

 (define set-of-final-states (apply set final-states)) ; Uses equal? for comparison of states.

 ; Define printf-tape before defining the struct-type for tapes.

 (define (print-tape tape port mode)
  (define head (reverse (tape-head tape)))
  (define tail (tape-tail tape))
  (write (list head tail) port))

 (struct tape (head tail)
  #:property prop:custom-write print-tape
  #:constructor-name make-tape
  #:omit-define-syntaxes)

 (define (tape-get tape) (car (tape-tail tape)))

 (define (tape-put tape tape-symbol)
  (when (equal? tape-symbol machine-blank)
   (error 'Turing-machine "machine-blank ~s not allowed to be written." machine-blank))
  (let ((head (tape-head tape)) (tail (tape-tail tape)))
   (cond
    ((null? tail) (make-tape head (list tape-symbol)))
    (else (make-tape head (cons tape-symbol (cdr tail)))))))

 (define (move-R tape)
  (let ((head (tape-head tape)) (tail (tape-tail tape)))
   (cond
    ((null? tail) (make-tape head (list machine-blank)))
    ((null? (cdr tail)) (make-tape (cons (car tail) head) (list machine-blank)))
    (else (make-tape (cons (car tail) head) (cdr tail))))))

 (define (move-L tape)
  (let ((head (tape-head tape)) (tail (tape-tail tape)))
   (cond
    ((null? head) (make-tape head (cons machine-blank tail)))
    (else (make-tape (cdr head) (cons (car head) tail))))))

 (define (list->tape lst)
  (if (null? lst)
   (make-tape '() (list machine-blank))
   (make-tape '() lst)))
 
 (define (tape->list tape)
  (remove-trailing-blanks
   (remove-heading-blanks
    (append (reverse (tape-head tape)) (tape-tail tape)))))
    
 (define (remove-heading-blanks lst)
  (cond
   ((null? lst) '())
   ((equal? (car lst) machine-blank) (remove-heading-blanks (cdr lst)))
   ((equal? (car lst) user-blank) (remove-heading-blanks (cdr lst)))
   (else lst)))

 (define (remove-trailing-blanks lst) (reverse (remove-heading-blanks (reverse lst))))
 
 (define (Turing-machine-proper state tape)
  (cond
   ((set-member? set-of-final-states state)
    (values state (tape->list tape)))
   (else
    (define old-tape-symbol (tape-get tape))
    (define-values (new-state new-tape-symbol move) (rules state (tape-get tape)))
    (define new-tape
     (case move
      ((R) (move-R (tape-put tape new-tape-symbol)))
      ((L) (move-L (tape-put tape new-tape-symbol)))
      ((N) (tape-put tape new-tape-symbol))))
    (when report?
     (printf "old state ~s, new state: ~s, tape-symbol ~s -> ~s, move: ~s, "
      state new-state old-tape-symbol new-tape-symbol move)
     (printf "new tape: ~s~n"
      (list (reverse (tape-head new-tape)) (tape-tail new-tape))))
    (Turing-machine-proper new-state new-tape))))
 
 (define initial-padding (make-string 51 #\.))

 (define (Turing-machine input)
  (unless (list? input)
   (error 'Turing-machine "list expected, given: ~s" input))
  (when (member machine-blank input)
   (error 'Turing-machine "machine-blank ~s not allowed in input" machine-blank))
  (define tape (list->tape input))
  (when report? (printf "~a initial tape: ~s~n" initial-padding tape))
  (Turing-machine-proper starting-state tape))

 Turing-machine)

;===================================================================================================
