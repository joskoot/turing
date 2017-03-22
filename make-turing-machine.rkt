#lang racket

(provide make-turing-machine)

#|==================================================================================================

Turing machine

The reader is supposed to be familiar with Turing machines. The combination of the tape and the
current position of the read/write-head is represented by two lists: head and tail. The content of
the represented tape is (append (reverse head) tail). The read/write-head of the tape always is upon
the first element of the tail, which never is empty. Initially the head is empty and the tail
contains the input. If the input is empty, the tail initially consists of one machine-blank. A move
is determined by the current state and the tape-symbol under the read/write-head. It consists of
assuming a new state, replacing the tape-symbol under the read/write-head and moving the
read/write-head one step to the right or to the left. The machine refuses to write machine-blanks,
but can write user-blanks. Machine-blanks are used only to extend the tape at the left or at the
right of the current content. When moving the tape head before the start or after the end of the
current content of the tape, a machine-blank is added and the read/write-head is positioned at this
machine-blank. In this way an infinite tape is simulated with an infinite number of machine-blanks
both at the left and at the right of the actual content. The machine repeats moves until a final
state is reached. The input must not contain machine-blanks. States and tape-symbols can be
arbitrary Racket values, but symbols and exact integer numbers are preferred. Procedure [equal?] is
used for comparison of two states or two tape-symbols.

Procedure: (make-turing-machine starting-state final-states report? machine-blank user-blank rules)
           -> turing-machine

Procedure: (turing-machine input) -> final-state output

starting-state : state
final-states   : (state ...)
machine-blank  : tape-symbol (not allowed to be written, for extension of the tape only)
user-blank     : tape-symbol (allowed to be written, must not be equal to machine-blank)
report?        : any/c
rules          : ((state (new-state tape-symbol move)) ...)
state          : any/c
new-state      : any/c
tape-symbol    : any/c
move           : R | L
turing-machine : (tape-symbol ...) -> (tape-symbol ...)
input          : (tape-symbol ...), but no machine-blanks.
output         : (tape-symbol ...)

When [report?] is not #f, each move is reported. Each line of the report shows the new state,
the tape-symbol that is written, the move being made (R for right or L for left) and the content of
the tape before the move was made. In the report the tape is written as (list (reverse head) tail),
blanks included. If no rule can be found for the current state and the tape-symbol below the
read/write-head, an exception is raised. Heading and trailing user-blanks and machine-blanks are
removed from the output before returning.

==================================================================================================|#

(define (make-turing-machine starting-state final-states report? machine-blank user-blank rules)

 (define (check-arguments) "Yet to do")

 (check-arguments)

 (define set-of-final-states (apply set final-states))

 (define (print-tape tape port mode)
  (define head (reverse (tape-head tape)))
  (define tail (tape-tail tape))
  (write (list head tail) port))

 (struct tape (head tail)
  #:property prop:custom-write print-tape
  #:constructor-name make-tape
  #:omit-define-syntaxes)

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
  (remove-blanks-at-end (remove-blanks (append (reverse (tape-head tape)) (tape-tail tape)))))
    
 (define (remove-blanks lst)
  (cond
   ((null? lst) '())
   ((equal? (car lst) machine-blank) (remove-blanks (cdr lst)))
   ((equal? (car lst) user-blank) (remove-blanks (cdr lst)))
   (else lst)))

 (define (remove-blanks-at-end lst) (reverse (remove-blanks (reverse lst))))
 
 (define (tape-get tape) (car (tape-tail tape)))

 (define (tape-put tape symbol)
  (when (equal? symbol machine-blank)
   (error 'turing-machine "machine-blank ~s not allowed to be written." machine-blank))
  (let ((head (tape-head tape)) (tail (tape-tail tape)))
   (cond
    ((null? tail) (make-tape head (list symbol)))
    (else (make-tape head (cons symbol (cdr tail)))))))

 (define (turing-machine state tape)
  (cond
   ((set-member? set-of-final-states state)
    (values state (tape->list tape)))
   (else
    (define-values (new-state symbol move) (find-rule state (tape-get tape) rules))
    (define new-tape
     (case move
      ((R) (move-R (tape-put tape symbol)))
      ((L) (move-L (tape-put tape symbol)))))
    (when report?
     (printf "old state ~s, new state: ~s, new tape-symbol: ~s, move: ~s, "
      state new-state symbol move)
     (printf "new content: ~s~n"
      (list (reverse (tape-head new-tape)) (tape-tail new-tape))))
    (turing-machine new-state new-tape))))
 
 (define (find-rule state symbol rules)
  (let ((entry (assoc state rules)))
   (unless entry (error 'turing-machine "unknown state: ~s" state))
   (let ((entry (assoc symbol (cdr entry))))
    (unless entry (error 'turing-machine "no rule for tape-symbol ~s in state ~s" symbol state))
    (apply values (cadr entry)))))

 (define (main input)
  (unless (list? input)
   (error 'turing-machine "list expected, given: ~s" input))
  (when (member machine-blank input)
   (error 'turing-machine "machine-blank ~s not allowed in input" machine-blank))
  (define tape (list->tape input))
  (when report? (printf "~a initial content: ~s~n" (make-string 51 #\.) tape))
  (turing-machine starting-state tape))

 main)

;===================================================================================================
