#lang racket

(provide make-tm)

#|==================================================================================================

Turing machine

The reader is supposed to be familiar with Turing machines.
The combination of the tape and the current position of the read/write-head
is represented by two lists: head and tail.
The content of the represented tape is (append (reverse head) tail).
The read/write-head of the tape always is at the first element of the tail, which never is empty.
The elements of the tape are called 'tape-symbol's
(in order to distinguish them from symbols of Racket)
Initially the head is empty and the tail contains the input.
If the input is empty, the tail initially consists of one blank.
A move is determined by the current state and the tape-symbol under the read/write-head.
A move consists of assuming a new state, replacing the tape-symbol under the read/write-head
and moving the read/write-head one step to the right or to the left.
The machine refuses to write blanks, but can write user-blanks.
Blanks are used only to extend the tape at the left or at the right of the current content.
When moving the tape head before the start or after the end of the current content of the tape,
a blank is added and the read/write-head is positioned at this blank.
In this way an infinite tape is simulated with an infinite number of blanks
both at the left and at the right of the actual content.
The machine repeats moves until a final state is reached.
The input must not contain blanks nor user-blanks.

States and tape-symbols can be anything, but symbols and exact integer numbers are preferred.
Procedure [equal?] is used for comparison of two states or two tape-symbols.

Procedure: (make-tm starting-state final-states blank user-blank report? rules) -> tm
starting-state : state
final-states   : (state ...)
report?        : any/c
blank          : tape-symbol (not allowed to be written, for extension the tape only)
user-blank     : tape-symbol (allowed to be written)
report?        : any/c
rules          : ((state (new-state tape-symbol move)) ...)
state          : any/c
tape-symbol    : any/c
move           : R | L
tm             : (tape-symbol ...) -> final-state result
result         : (tape-symbol ...)

The produced tm removes blanks and user-blanks preceding the content
and those following the content before returning the result. 

When [report?] is not #f, each move is reported.
Each line of the report shows the new state,
the tape-symbol that is written,
the move being made (R for right or L for left)
and the content of the tape before the move was made.
In the report the tape is written as (list (reverse head) tail), blanks included.
If no rule can be found for the current state and the tape-symbol below the read/write-head,
an exception is raised.
The returned list (tape-symbol ...) does not contain heading nor trailing blanks or user-blanks,
but may contain other user-blanks.

==================================================================================================|#

(define (make-tm starting-state final-states report? blank user-blank rules)

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
    ((null? tail) (make-tape head (list blank)))
    ((null? (cdr tail)) (make-tape (cons (car tail) head) (list blank)))
    (else (make-tape (cons (car tail) head) (cdr tail))))))

 (define (move-L tape)
  (let ((head (tape-head tape)) (tail (tape-tail tape)))
   (cond
    ((null? head) (make-tape head (cons blank tail)))
    (else (make-tape (cdr head) (cons (car head) tail))))))

 (define (list->tape lst)
  (if (null? lst) (make-tape '() (list blank)) (make-tape '() lst)))
 
 (define (tape->list tape)
  (define head (remove-blanks (reverse (tape-head tape))))
  (define tail (reverse (remove-blanks (reverse (tape-tail tape)))))
  (if (null? head) (remove-blanks tail) (append head tail)))
    
 (define (remove-blanks lst)
  (cond
   ((null? lst) '())
   ((eq? (car lst) blank) (remove-blanks (cdr lst)))
   ((eq? (car lst) user-blank) (remove-blanks (cdr lst)))
   (else lst)))
 
 (define (tape-get tape) (let ((tail (tape-tail tape))) (if (null? tail) blank (car tail))))

 (define (tape-put tape symbol)
  (when (equal? symbol blank) (error 'tm "blank ~s not allowed to be written." blank))
  (let ((head (tape-head tape)) (tail (tape-tail tape)))
   (cond
    ((null? tail) (make-tape head (list symbol)))
    (else (make-tape head (cons symbol (cdr tail)))))))

 (define (tm state tape)
  (cond
   ((set-member? set-of-final-states state)
    (when report? (printf "            final state ~s~n" state))
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
    (tm new-state new-tape))))
 
 (define (find-rule state symbol rules)
  (let ((entry (assoc state rules)))
   (unless entry (error 'tm "unknown state: ~s" state))
   (let ((entry (assoc symbol (cdr entry))))
    (unless entry (error 'tm "no rule for state ~s with symbol ~s" state symbol))
    (apply values (cadr entry)))))

 (define (is-blank? x) (or (equal? x blank) (equal? x user-blank)))
 
 (λ (lst)
  (unless (list? lst)
   (error tm "list expected, given: ~s" lst))
  (when (member blank lst)
   (error 'tm "blank ~s not allowed in input" blank))
  (when (member user-blank lst)
   (error 'tm "user-blank ~s not allowed in input" user-blank))
  (define tape (list->tape lst))
  (when report? (printf "~ainitial content: ~s~n" (make-string 52 #\space) tape))
  (tm starting-state tape)))

;===================================================================================================
