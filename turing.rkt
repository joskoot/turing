#lang racket

#|==================================================================================================

Turing machine

The combination of the tape and the current position of the read/write-head
is represented by two lists called head and tail.
The content of the represented tape is (append (reverse head) tail).
The read/write-head of the tape always is at the first element of the tail.
Initially the head is empty and the tail contains the input.
The tail is never empty. If the input is empty, the tail initially consists of one blank.
The elements of the tape are called 'tape-symbol's
(in order to distinguish them from symbols of Racket)
A move is determined by the current state and the tape-symbol under the read/write-head.
A move consists of assuming a new state, replacing the tape-symbol under the read/write-head
and moving the read/write-head one step to the right or to the left.
When moving the tape head before the start or after the end of the tape,
a blank is added and the read/write-head is positioned at this blank.
The machine repeats moves until a final state is reached.
The machine must not write blanks, but can write allowed-blanks.
The input must not contain blanks nor allowed-blanks.

States and tape-symbols can be anything, but symbols and exact integer numbers are preferred.
Procedure [equal?] is used for comparison of states and tape-symbols.

Procedure: (make-tm starting-state final-states blank allowed-blank report? padding rules)
           -> tm
starting-state : state
final-states   : (state ...)
report?        : any/c
blank          : tape-symbol (not allowed to be written)
allowed-blank  : tape-symbol (allowed to be written)
report?        : any/c
padding        : exact integer
rules          : ((state (new-state tape-symbol move)) ...)
state          : any/c
tape-symbol    : any/c
move           : R | L
tm             : (tape-symbol ...) -> final-state (tape-symbol ...)

When [report?] is not #f, each move is reported printing the tape as (list (reverse head) tail).
Padding is used to pad printing the tape with trailing spaces (used only when [report?] is not #f)
In the report the tape is written as (list (reverse head) tail), blanks included.
The blank is a tape-symbol. It is not allowed to write a blank.
The allowed-blank is considered to be a blank too. It may be written.
If no rule can be found for the current state and the tape-symbol below the read/write-head,
an exception is raised.
The returned list (tape-symbol ...) does not contain heading nor trailing blanks or allowed-blanks,
but may contain other allowed-blanks.

==================================================================================================|#

(define (make-tm starting-state final-states report? blank allowed-blank padding rules)

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
  (define head (remove-blanks (tape-head tape)))
  (define tail (reverse (remove-blanks (reverse (tape-tail tape)))))
  (if (null? head) (remove-blanks tail) (append head tail)))
    
 (define (remove-blanks lst)
  (cond
   ((null? lst) '())
   ((eq? (car lst) blank) (remove-blanks (cdr lst)))
   ((eq? (car lst) allowed-blank) (remove-blanks (cdr lst)))
   (else lst)))
 
 (define (tape-get tape) (let ((tail (tape-tail tape))) (if (null? tail) blank (car tail))))

 (define (tape-put tape symbol)
  (when (equal? symbol blank) (error 'tm "blank ~s not allowed to be written." blank))
  (let ((head (tape-head tape)) (tail (tape-tail tape)))
   (cond
    ((null? tail) (make-tape head (list symbol)))
    (else (make-tape head (cons symbol (cdr tail)))))))

 (define (tm state tape)
  (when report? (printf "state: ~a, tape: ~a, " state (pad tape padding)))
  (cond
   ((set-member? set-of-final-states state)
    (when report? (printf "final state ~s~n" state))
    (values state (tape->list tape)))
   (else
    (define-values (new-state symbol move) (find-rule state (tape-get tape) rules))
    (when report?
     (printf "rule: new-state ~s, new tape-symbol: ~s, move: ~s~n" new-state symbol move))
    (case move
     ((R) (tm new-state (move-R (tape-put tape symbol))))
     ((L) (tm new-state (move-L (tape-put tape symbol))))))))
 
 (define (find-rule state symbol rules)
  (let ((entry (assoc state rules)))
   (unless entry (error 'tm "unknown state: ~s" state))
   (let ((entry (assoc symbol (cdr entry))))
    (unless entry (error 'tm "no rule for state ~s with symbol ~s" state symbol))
    (apply values (cadr entry)))))

 (define (pad x n)
  (define y (format "~s" x))
  (string-append y (make-string (max 0 (- n (string-length y))) #\space)))

 (define (is-blank? x) (or (equal? x blank) (equal? x allowed-blank)))
 
 (λ (lst)
  (unless (list? lst)
   (error tm "list expected, given: ~s" lst))
  (when (member blank lst)
   (error 'tm "blank ~s not allowed in input" blank))
  (when (member allowed-blank lst)
   (error 'tm "allowed-blank ~s not allowed in input" allowed-blank))
  (tm starting-state (list->tape lst))))

;===================================================================================================

; The following tm terminates for every list of symbols x and +.
; A correct input is (x ... [+ x ...]).
; The result of a correct input is the input without +.
; This is like adding two natural numbers.
; Without + the tm returns the input.
; When encountering a + it is replaced by x and at the end one x will be erased.
; A correct input halts with state T.
; An erroneous input containing no other tape-symbols than x and + halts in state F.
; An input containing any other tape-symbol than x or + causes an error to be raised.

(define tm
 (make-tm '0 '(T F) #t 'B 'b 23 ; T/F final state for accepted/rejected input.
 '((0               ; Initial state. No + encountered yet.
    (x (0 x R))            
    (+ (1 x R))            ; Replace + by x. At end one x will be erased.
    (B (3 b L)))           ; The input has no + and is accepted. Go rewind the tape.
   (1               ; A + has been encountered.
    (x (1 x R)) 
    (+ (F + L))            ; After + do not accept a second +.
    (B (2 b L)))           ; Go erase an x in order to account for the x produced by +.
   (2               ; Erase one x. In this state the current tape-symbol always is x.
    (x (3 b L)))           ; Go rewind the tape.
   (3               ; Rewind the tape (just for pleasure)
    (x (3 x L))            ; Keep on rewinding.
    (B (T b R))))))        ; Accept the input.

(define (test lst expected-state expected-tape)
 (set! nr-of-tests (add1 nr-of-tests))
 (let/ec ec
  (parameterize
   ((error-escape-handler
     (λ () (newline) (set! nr-of-errors (add1 nr-of-errors)) (ec))))
   (with-handlers ((exn:fail? (λ (exn) (newline) (raise exn))))
    (define-values (state tape) (tm lst))
    (unless (and (equal? state expected-state) (equal? tape expected-tape))
     (fprintf (current-error-port) "Wrong result~n")
     (set! nr-of-failures (add1 nr-of-failures)))
    (values state tape)))))

(define (test-report)
 (printf "nr of tests: ~s~n" nr-of-tests)
 (printf "nr-of-failures (errors not included): ~s~n" nr-of-failures)
 (printf "nr-of-errors: ~s~n" nr-of-errors)
 (set! nr-of-tests 0)
 (set! nr-of-failures 0))

(define nr-of-tests 0)
(define nr-of-failures 0)
(define nr-of-errors 0)

(test '(x x x + x x) 'T '(x x x x x))
(test '(x x x +)     'T '(x x x))
(test '(+ x x)       'T '(x x))
(test '(+)           'T '())
(test '(x x x x x)   'T '(x x x x x))
(test '(x)           'T '(x))
(test '()            'T '())
(test '(+ +)         'F '(x +))
(test '(+ x +)       'F '(x x +))
(test '(x x + x + x) 'F '(x x x x + x))

(test-report)

(eprintf "~nThe following errors are expected.~n")

(test '(B) 'T '())
(test '(b) 'T '())
(test '(y) 'F '())
(test '(x x x y x x ) 'F '())
(test '(x + x y x) 'F '())

(printf "~nThe following test report should show as many errors as tests.~n")
(test-report)
;===================================================================================================
