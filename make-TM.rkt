#lang racket

(provide make-TM)

;==================================================================================================

(define (make-TM
         init-state
         final-states
         empty space dummy
         rules
         #:registers (reg-names 2)
         #:name (name 'TM-without-name))
        
 (define
  (TM
   input
   #:registers (register-values #f)
   #:report (report #f)
   #:limit (limit #f)) 

  (check-input input)
  (check-limit limit)
  (check-report report)
  (when register-values (check-register-values register-values))
  (define move-counter 0)
  (define tape (list->tape input))
  
  (define (inner-TM)
   (when report
    (printf
     (string-append
      "~a~nReport of ~s~n~a~n"
      "initial tape content: ~s~n"
      "initial registers   : ~s~n"
      "~a~n")
     line
     name
     line
     tape
     (map get-register register-names)
     line))
   (define final-state (TM-proper))
   (when report (printf "~s halted in final state ~s~nEnd of report.~n~a~n" name final-state line))
   (define tape* (tape->list tape))
   (set! tape #f)
   (set! register-hash #f)
   (values move-counter final-state tape*))

  (define (TM-proper)
   (define old-state (hash-ref register-hash state-key))
   (cond
    ((set-member? final-states-set old-state) old-state)
    ((and limit (>= move-counter limit))
     (error name
      "~nAbout to exceed the max nr of moves:~n~
       move: ~s~n~
       tape: ~s~n~
       registers: ~s~n"
      move-counter
      tape
      (map get-register register-names)))
    (else
     (define datum (tape-read))
     (hash-set! register-hash databus datum)
     (define old-register-values (map get-register register-names))
     (set! move-counter (add1 move-counter))
     (define (rule-error) (rule-error* old-state datum old-register-values))
     (define (get-dummy-rule) (hash-ref dummy-rules-hash old-state rule-error))
     (define rule (hash-ref normal-rules-hash (list old-state datum) get-dummy-rule))
     (define new-register-values (map get-register-value* (rule-new-registers rule) register-names))
     (define move (rule-move rule))
     (set! register-hash (make-hash (map cons register-names new-register-values)))
     (define new-datum (cadr new-register-values))
     (tape-write new-datum)
     (case move
      ((L) (move-left))
      ((R) (move-right))
      (else (void)))
     (case report
      ((#t long)
       (printf
        (string-append
         "move nr  : ~s~n"
         "rule     : ~s~n"
         "registers: ~s -> ~s~n"
         "move     : ~s~n"
         "new tape : ~s~n"
         "~a~n")
        move-counter
        rule
        old-register-values new-register-values
        move
        tape
        line))
      ((short)
       (printf "~s, state ~s -> ~s, ~s~n"
        move-counter (car old-register-values) (car new-register-values) tape)))
     (TM-proper))))
 
  (define state-key (car register-names))
  (define databus (cadr register-names))
  (define (tape-read) (car (tape-tail tape)))
  
  (define register-hash
   (if register-values
    (make-hasheq (map cons register-names register-values))
    (make-hasheq
     (cons (cons state-key init-state)
           (map (λ (x) (cons x empty)) (cdr register-names))))))
  
  (define (get-register state) (if (keyword? state) (hash-ref register-hash state) state))
  
  (define (get-register-value* register-value register-name)
   (cond
    ((keyword? register-value) (hash-ref register-hash register-value))
    ((equal? register-value dummy) (hash-ref register-hash register-name))
    (else register-value)))
  
  (define (tape-write datum)
   (set-tape-tail! tape (cons (empty->space datum) (cdr (tape-tail tape)))))
  
  (define-values (normal-rules-hash dummy-rules-hash)
   (for/fold
    ((normal-rules-hash (make-immutable-hash)) (dummy-rules-hash (make-immutable-hash)))
    ((rule (in-list rules)))
    (if (normal-rule? rule)
     (values
      (hash-set normal-rules-hash (rule-selector rule) rule)
      dummy-rules-hash)
     (values
      normal-rules-hash
      (hash-set dummy-rules-hash (rule-old-state rule) rule)))))
 
  (define (rule-error* old-state datum register-values)
   (error name
    "~nNo rule for state ~s and tape-element ~s~n~
     move: ~s~n~
     tape: ~s~n~
     registers: ~s~n"
    old-state datum
    move-counter
    tape
    register-values))
 
  (define (move-left)
   (define reversed-head (tape-reversed-head tape))
   (define tail (tape-tail tape))
   (cond
    ((null? reversed-head)
     (set-tape-reversed-head! tape '())
     (set-tape-tail! tape (cons empty tail)))
    (else
     (set-tape-reversed-head! tape (cdr reversed-head))
     (set-tape-tail! tape (cons (car reversed-head) tail)))))
       
  (define (move-right)
   (let ((reverse-head (tape-reversed-head tape)) (tail (tape-tail tape)))
    (cond
     ((null? (cdr tail))
      (set-tape-reversed-head! tape (cons (car tail) reverse-head))
      (set-tape-tail! tape (list empty)))
     (else
      (set-tape-reversed-head! tape (cons (car tail) reverse-head))
      (set-tape-tail! tape (cdr tail))))))

  (inner-TM))

 (define final-states-set (apply set final-states))
 
 (define (check-arguments)
  (unless (symbol? name) (raise-argument-error 'make-TM "symbol?" name))
  (define (dummy? x) (equal? x dummy))
  (define (empty? x) (equal? x empty))
  (define (state/datum? x) (and (not (keyword? x)) (not (equal? x dummy))))
  (define (register? x) (or (member x register-names) (not (keyword? x))))
  (define (rule? x)
   (and (list? x) (= (length x) 3)
    (let ((select (car x)) (move (caddr x)) (new-registers (cadr x)))
     (and (list? select) (= (length select) 2)
      (let
       ((old-state (car select))
        (old-symbol (cadr select)))
       (and
        (state/datum? old-state)
        (or (state/datum? old-symbol) (dummy? old-symbol))
        (and
         (list? new-registers)
         (= (length new-registers) nr-of-registers)
         (andmap register? new-registers)
         (member move '(L R N)))))))))

  ; Body of make-TM
  
  (unless (state/datum? init-state) (error 'make-TM "incorrect initial state: ~s" init-state))
  (unless (and (list? final-states) (andmap state/datum? final-states))
   (error 'make-TM "incorrect list of final states: ~s" final-states))
  (when (keyword? dummy) (raise-argument-error 'make-TM "(not/c keyword?)" dummy))
  (when (keyword? empty) (raise-argument-error 'make-TM "(not/c keyword?)" empty))
  (when (keyword? space) (raise-argument-error 'make-TM "(not/c keyword?)" space))
  (when (or (equal? dummy space) (equal? dummy empty) (equal? space empty))
   (error 'make-TM "dummy space and empty must be distinct, given: ~s ~s ~s" dummy space empty))
  (unless (list? rules) (raise-argument-error 'make-TM "list of rules" rules))
  (for ((rule (in-list rules)) #:unless (rule? rule)) (error 'make-TM "incorrect rule: ~s" rule))
  (unless
   (or
    (and (exact-positive-integer? reg-names) (>= reg-names 2))
    (and (list? reg-names)
         (pair? reg-names)
         (andmap keyword? reg-names)
         (not (check-duplicates reg-names))))
   (error 'make-TM "incorrect registers: ~s" reg-names)))

 (define register-names
  (if (exact-positive-integer? reg-names)
   (build-list reg-names make-reg-name)
    reg-names))
 
 (define nr-of-registers (length register-names))
 
 (check-arguments)

 ; Procedures for use in TM, inner-TM and TM-proper

 (define (normal-rule? rule) (not (equal? (rule-old-datum rule) dummy)))
 (define (empty->space datum) (if (equal? datum empty) space datum))
 
 (define (list->tape lst)
  (if (null? lst)
   (make-tape '() (list empty))
   (make-tape '() lst)))
  
 (define (tape->list tape)
  (remove-trailing-spaces
   (remove-heading-spaces
    (append (reverse (tape-reversed-head tape)) (tape-tail tape)))))

 (define (remove-heading-spaces lst)
  (cond
   ((null? lst) '())
   ((equal? (car lst) empty) (remove-heading-spaces (cdr lst)))
   ((equal? (car lst) space) (remove-heading-spaces (cdr lst)))
   (else lst)))
 
 (define (remove-trailing-spaces lst) (reverse (remove-heading-spaces (reverse lst))))
 
 (define (check-input input)
  (unless
   (and
    (list? input)
    (not (member empty input))
    (not (member dummy input))
    (not (ormap keyword? input)))
   (error name "incorrect input: ~s" input)))
 
 (define (check-register-values register-values)
  (unless
   (and
    (= (length register-values) nr-of-registers)
    (not (ormap keyword? register-values))
    (not (member dummy register-values)))
   (error name "incorrect registers: ~s" register-values)))
 
 (define (check-limit x)
  (unless (or (eq? x #f) (exact-positive-integer? x))
   (error name "incorrect limit: ~s" x)))

 (define (check-report report)
  (unless (member report '(#f #t short long))
   (error name "incorrect report argument: ~s" report)))
 
 (procedure-rename TM name))

;==================================================================================================

(define (print-tape tape port mode)
 (write (list (reverse (tape-reversed-head tape)) (tape-tail tape)) port))

; print-tape must be defined before struct tape.

(struct tape (reversed-head tail)
 #:mutable
 #:property prop:custom-write print-tape
 #:constructor-name make-tape
 #:omit-define-syntaxes)
 
(define (make-reg-name n) (string->keyword (format "~s" n)))
(define rule-selector car)
(define rule-old-state caar)
(define rule-old-datum cadar)
(define rule-new-registers cadr)
(define rule-move caddr)
(define line "------------------------------------------------------")

;==================================================================================================
