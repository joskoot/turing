#lang racket

(provide make-Turing-machine Turing-report Turing-limit Turing-pad)

#|==================================================================================================

Module make-Turing-machine.scrbl produces documentation.

==================================================================================================|#

(define Turing-report (make-parameter #f (λ (x) (and x #t))))
(define (Turing-limit-guard x) (if (exact-positive-integer? x) x #f))
(define Turing-limit (make-parameter #f Turing-limit-guard))

(define (move-counter-width-guard x)
 (if (exact-nonnegative-integer? x) x
  (raise-argument-error 'Turing-pad "exact-nonnegative-integer" x)))

(define Turing-pad (make-parameter 0 move-counter-width-guard))

(define (make-Turing-machine
         initial-state
         final-states
         empty-cell
         blank
         dummy rules)

 (define (rule-old-state rule) (car (car rule)))
 (define (rule-old-symbol rule) (cadr (car rule)))
 (define (rule-new-state rule) (car (cadr rule)))
 (define (rule-new-symbol rule) (cadr (cadr rule)))
 (define (rule-move rule) (caddr (cadr rule)))

 (define (check-arguments)
  ; There may be more than one error. Only the first one detected is raised.
  (define (rule? x)
   (and
    (list? x)
    (= (length x) 2)
    (list? (car x)) (= (length (car x)) 2)
    (list? (cadr x)) (= (length (cadr x)) 3)
    (let*
     ((new-state (rule-new-state x))
      (move (rule-move x)))
     (and
      (member move '(R L N))
      (not (equal? new-state empty-cell))))))
  (when (equal? empty-cell blank)
   (error 'make-Turing-machine "empty-cell must differ from blank: ~s" blank))
  (unless (list? final-states)
   (error 'make-Turing-machine "incorrect argument for final-states: ~s" final-states))
  (unless (list? rules)
   (error 'make-Turing-machine "incorrect argument for rules: ~s" rules))
  (for ((rule (in-list rules)))
   (unless (rule? rule)
    (error 'make-Turing-machine "incorrect rule: ~s" rule)))
  (define duplicate (check-duplicates (map car rules)))
  (when duplicate
   (error 'make-Turing-machine "duplicate move-selector: ~s" duplicate)))

 (check-arguments)

 (define (print-width x) (string-length (format "~s" x)))

 (define-values
  (old-state-width new-state-width old-symbol-width* new-symbol-width* old-dummy? new-dummy?)
  (for/fold
   ((old-state-width 0)
    (new-state-width 0)
    (old-symbol-width 0)
    (new-symbol-width 0)
    (old-dummy? #f)
    (new-dummy? #f))
   ((rule (in-list rules)))
   (values
    (max old-state-width (print-width (rule-old-state rule)))
    (max new-state-width (print-width (rule-new-state rule)))
    (max old-symbol-width (print-width (rule-old-symbol rule)))
    (max new-symbol-width (print-width (rule-new-symbol rule)))
    (or old-dummy? (equal? (rule-old-symbol rule) dummy))
    (or new-dummy? (equal? (rule-new-symbol rule) dummy)))))

 (define old-symbol-width
  (if old-dummy?
   (max old-symbol-width* new-symbol-width*)
   old-symbol-width*))

 (define new-symbol-width
  (if new-dummy?
   (max old-symbol-width* new-symbol-width*)
   new-symbol-width*))

 (define (pad-old-state state) (pad state old-state-width))
 (define (pad-new-state state) (pad state new-state-width))
 (define (pad-old-symbol symbol) (pad symbol old-symbol-width))
 (define (pad-new-symbol symbol) (pad symbol new-symbol-width))
 
 (define (pad x n)
  (define str (format "~s" x))
  (string-append (make-string (max 0 (- n (string-length str))) #\space) str))

 (define set-of-final-states (apply set final-states)) ; Uses equal? for comparison of states.

 ; Define printf-tape before defining the struct-type for tapes.

 (define (print-tape tape port mode)
  (define head (reverse (tape-reversed-head tape)))
  (define tail (tape-tail tape))
  (write (list head tail) port))

 (struct tape (reversed-head tail)
  #:property prop:custom-write print-tape
  #:constructor-name make-tape
  #:omit-define-syntaxes
  #:transparent)

 (define (tape-get tape) (car (tape-tail tape)))

 (define (tape-put tape tape-symbol)
  (when (equal? tape-symbol empty-cell)
   (error 'Turing-machine "empty-cell ~s not allowed to be written." empty-cell))
  (let ((reversed-head (tape-reversed-head tape)) (tail (tape-tail tape)))
   (cond
    ((null? tail) (make-tape reversed-head (list tape-symbol)))
    (else (make-tape reversed-head (cons tape-symbol (cdr tail)))))))

 (define (move-R tape)
  (let ((reversed-head (tape-reversed-head tape)) (tail (tape-tail tape)))
   (cond
    ((null? tail) (make-tape reversed-head (list empty-cell)))
    ((null? (cdr tail)) (make-tape (cons (car tail) reversed-head) (list empty-cell)))
    (else (make-tape (cons (car tail) reversed-head) (cdr tail))))))

 (define (move-L tape)
  (let ((reversed-head (tape-reversed-head tape)) (tail (tape-tail tape)))
   (cond
    ((null? reversed-head) (make-tape reversed-head (cons empty-cell tail)))
    (else (make-tape (cdr reversed-head) (cons (car reversed-head) tail))))))

 (define (list->tape lst)
  (if (null? lst)
   (make-tape '() (list empty-cell))
   (make-tape '() lst)))
 
 (define (tape->list tape)
  (remove-trailing-blanks
   (remove-heading-blanks
    (append (reverse (tape-reversed-head tape)) (tape-tail tape)))))
    
 (define (remove-heading-blanks lst)
  (cond
   ((null? lst) '())
   ((equal? (car lst) empty-cell) (remove-heading-blanks (cdr lst)))
   ((equal? (car lst) blank) (remove-heading-blanks (cdr lst)))
   (else lst)))

 (define (remove-trailing-blanks lst) (reverse (remove-heading-blanks (reverse lst))))

 (define (Turing-machine-proper state tape)
  (cond
   ((set-member? set-of-final-states state)
    (values nr-of-moves state (tape->list tape)))
   (else
    (set! nr-of-moves (add1 nr-of-moves))
    (define old-tape-symbol (tape-get tape))
    (define-values (new-state new-tape-symbol move) (find-rule state (tape-get tape) tape))
    (define new-tape
     (case move
      ((R) (move-R (tape-put tape new-tape-symbol)))
      ((L) (move-L (tape-put tape new-tape-symbol)))
      ((N) (tape-put tape new-tape-symbol))))
    (when (Turing-report)
     (printf "move ~a, state ~a -> ~a, symbol ~a -> ~a, move ~s, new tape ~s~n"
      (pad-move-counter nr-of-moves)
      (pad-old-state state)
      (pad-new-state new-state)
      (pad-old-symbol old-tape-symbol)
      (pad-new-symbol new-tape-symbol)
      move
      new-tape))
    (when
     (and
      (Turing-limit)
      (>= nr-of-moves (Turing-limit))
      (not (set-member? final-states new-state)))
     (error 'Turing-machine
      "no final state within max nr of moves~n~
       move-counter: ~s~n~
       current state: ~s~n~
       current content: ~s"
      nr-of-moves
      new-state
      new-tape))
    (Turing-machine-proper new-state new-tape))))

 (define (pad-move-counter n)
  (define str (format "~s" n))
  (string-append
   (make-string (max 0 (- (Turing-pad) (string-length str))) #\space)
   str))

 (define nr-of-moves #f)

 (define-values (normal-hash dummy-hash)
  (let ()
   (define-values (dummy-rules normal-rules)
    (for/fold ((dr '()) (nr '())) ((rule (in-list rules)))
     (if (equal? (cadar rule) dummy)
      (values (cons rule dr) nr)
      (values dr (cons rule nr)))))
   (define normal-hash (make-hash (map (λ (x) (cons (car x) (cadr x))) normal-rules)))
   (define dummy-hash (make-hash (map (λ (x) (cons (caar x) (cadr x))) dummy-rules)))
   (values normal-hash dummy-hash)))

 (define (find-rule state tape-symbol tape)
  (define (avoid-empty-cell tape-symbol)
   (if (eq? tape-symbol empty-cell) blank tape-symbol))
  (define normal-rule (hash-ref normal-hash (list state tape-symbol) #f))
  (cond
   ((not normal-rule)
    (define dummy-rule (hash-ref dummy-hash state #f))
    (cond
     ((not dummy-rule)
      (error 'Turing-machine
       "no rule for state: ~s, with symbol: ~s~n~
        current content: ~s"
       state tape-symbol
       tape))
     (else
      (define new-state (car dummy-rule))
      (define new-symbol (cadr dummy-rule))
      (define move (caddr dummy-rule))
      (cond
       ((equal? new-symbol dummy)
        (values new-state (avoid-empty-cell tape-symbol) move))
       (else (values new-state new-symbol move))))))
   (else
    (define new-state (car normal-rule))
    (define new-symbol (cadr normal-rule))
    (define move (caddr normal-rule))
    (cond
     ((equal? new-symbol dummy)
      (values new-state (avoid-empty-cell tape-symbol) move))
     (else (values new-state new-symbol move))))))

 (define initial-padding-length
  (+ 36
   (max 1 old-symbol-width)
   (max 1 new-symbol-width)
   (max 1 old-state-width)
   (max 1 new-state-width)))

 (define initial-padding #f)

 (define (Turing-machine input)
  (unless (list? input)
   (error 'Turing-machine "list expected, given: ~s" input))
  (when (member empty-cell input)
   (error 'Turing-machine "empty-cell ~s not allowed in input" empty-cell))
  (when (member dummy input)
   (error 'Turing-machine "dummy ~s not allowed in input" dummy))
  (define tape (list->tape input))
  (when (Turing-report)
   (set! initial-padding
    (make-string (+ initial-padding-length (min 1 (Turing-pad))) #\.))
   (printf "~a initial tape ~s~n" initial-padding tape))
  (set! nr-of-moves 0)
  (Turing-machine-proper initial-state tape))

 Turing-machine)

;===================================================================================================
