#lang racket

(provide make-TM)

;==================================================================================================

(define (make-TM
         init-state
         final-states
         empty blank dummy
         rules
         #:state-registers (state-regs 1)
         #:data-registers (data-regs 1)
         #:name (name 'TM-without-name))

 (define
  (TM
   input
   #:state-registers (states #f)
   #:data-registers (data #f)
   #:report (report #f)
   #:limit (limit #f)) 

  (check-input input)
  (check-limit limit)
  (when states (check-states states))
  (when data (check-data data))
  (define move-counter 0)
  (define tape (list->tape input))
  
  (define (TM)
   (when report
    (printf
     (string-append
      "~a~nReport of ~s~n~a~n"
      "initial tape content   : ~s~n"
      "initial state registers: ~s~n"
      "initial data registers : ~s~n"
      "~a~n")
     line
     name
     line
     tape
     (map get-state state-reg-names)
     (map get-datum data-reg-names)
     line))
   (define final-state (TM-proper))
   (when report (printf "~s halted in final state ~s~nEnd of report.~n~a~n" name final-state line))
   (define tape* (tape->list tape))
   (set! tape #f)
   (set! data-reg-hash #f)
   (set! state-reg-hash #f)
   (values move-counter final-state tape*))

  (define (TM-proper)
   (define old-state (hash-ref state-reg-hash state-reg))
   (cond
    ((set-member? final-states-set old-state) old-state)
    ((and limit (>= move-counter limit))
     (error name
      "~nAbout to exceed the max nr of moves:~n~
       move: ~s~n~
       tape: ~s~n~
       state-registers: ~s~n~
       data-registers: ~s~n"
      move-counter
      tape
      (map get-state state-reg-names)
      (map get-datum data-reg-names)))
    (else
     (define datum (tape-read))
     (hash-set! data-reg-hash databus datum)
     (define old-states (map get-state state-reg-names))
     (define old-data (map get-datum data-reg-names))
     (set! move-counter (add1 move-counter))
     (define (rule-error) (rule-error* old-state datum old-states old-data))
     (define (get-dummy-rule) (hash-ref dummy-rules-hash old-state rule-error))
     (define rule (hash-ref normal-rules-hash (list old-state datum) get-dummy-rule))
     (define instr (rule-instr rule))
     (define new-states (map get-state* (instr-new-states instr) state-reg-names))
     (define new-data (map get-datum* (instr-new-data instr) data-reg-names))
     (define new-state (car new-states))
     (define move (instr-move instr))
     (set! state-reg-hash (make-hash (map cons state-reg-names new-states)))
     (set! data-reg-hash (make-hash (map cons data-reg-names new-data)))
     (define new-datum (car new-data))
     (tape-write new-datum)
     (case move
      ((L) (move-left))
      ((R) (move-right))
      (else (void)))
     (case report
      ((#t long)
       (printf
        (string-append
         "move number    : ~s~n"
         "rule           : ~s~n"
         "state registers: ~s -> ~s~n"
         "data registers : ~s -> ~s~n"
         "move           : ~s~n"
         "new tape       : ~s~n"
         "~a~n")
        move-counter
        rule
        old-states new-states
        old-data new-data
        move
        tape
        line))
      ((short)
       (printf "~s, state ~s -> ~s, ~s~n"
        move-counter (car old-states) (car new-states) tape)))
     (TM-proper))))
 
  (define state-reg-hash
   (if states
    (make-hasheq (map cons state-reg-names states))
    (make-hasheq (map (λ (x) (cons x init-state)) state-reg-names))))
  
  (define data-reg-hash
   (if data
    (make-hasheq (map cons data-reg-names data))
    (make-hasheq (map (λ (x) (cons x empty)) data-reg-names))))

  (define (get-state state) (if (keyword? state) (hash-ref state-reg-hash state) state))
  (define (get-datum datum) (if (keyword? datum) (hash-ref data-reg-hash datum) datum))
  
  (define (get-state* state reg)
   (cond
    ((keyword? state) (hash-ref state-reg-hash state))
    ((equal? state dummy) (hash-ref state-reg-hash reg))
    (else state)))
  
  (define (get-datum* datum reg)
   (cond
    ((keyword? datum) (hash-ref data-reg-hash datum))
    ((equal? datum dummy) (hash-ref data-reg-hash reg))
    (else datum)))
  
  (define state-reg (car state-reg-names))
  (define databus (car data-reg-names))
  (define (tape-read) (car (tape-tail tape)))
  
  (define (tape-write datum)
   (set-tape-tail! tape (cons (empty->blank datum) (cdr (tape-tail tape)))))
  
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
 
  (define (rule-error* old-state datum old-states old-data)
   (error name
    "~nNo rule for state ~s and tape-element ~s~n~
     move: ~s~n~
     tape: ~s~n~
     state-registers: ~s~n~
     data-registers: ~s~n"
    old-state datum
    move-counter
    tape
    old-states
    old-data))
 
  (define (move-left)
   (define reversed-head (tape-rev-head tape))
   (define tail (tape-tail tape))
   (cond
    ((null? reversed-head)
     (set-tape-rev-head! tape '())
     (set-tape-tail! tape (cons empty tail)))
    (else
     (set-tape-rev-head! tape (cdr reversed-head))
     (set-tape-tail! tape (cons (car reversed-head) tail)))))
       
  (define (move-right)
   (let ((reverse-head (tape-rev-head tape)) (tail (tape-tail tape)))
    (cond
     ((null? (cdr tail))
      (set-tape-rev-head! tape (cons (car tail) reverse-head))
      (set-tape-tail! tape (list empty)))
     (else
      (set-tape-rev-head! tape (cons (car tail) reverse-head))
      (set-tape-tail! tape (cdr tail))))))

  (TM))

 (define final-states-set (apply set final-states))
 
 (define state-reg-names
  (if (exact-positive-integer? state-regs)
   (build-list state-regs make-reg-name)
   state-regs))
 
 (define data-reg-names
  (if (exact-positive-integer? data-regs)
   (build-list data-regs make-reg-name)
   data-regs))

 (define (check-arguments)
  (unless (symbol? name) (raise-argument-error 'make-TM "symbol?" name))
  (define (dummy? x) (equal? x dummy))
  (define (empty? x) (equal? x empty))
  (define (state? x) (and (not (keyword? x)) (not (equal? x dummy))))
  (define (tape-element? x) (and (not (keyword? x)) (not (equal? x dummy))))
  (define (tape-symbol? x) (and (tape-element? x) (not (equal? x empty))))
  (define (new-state? x) (or (member x state-reg-names) (not (keyword? x))))
  (define (new-datum? x) (or (member x data-reg-names) (not (keyword? x))))
  (define (rule? x)
   (and (list? x) (= (length x) 2)
    (let ((select (car x)) (instr (cadr x)))
     (and (= (length select) 2) (= (length instr) 3)
      (let
       ((old-state (car select))
        (old-symbol (cadr select))
        (new-states (car instr))
        (new-data (cadr instr))
        (move (caddr instr)))
       (and
        (state? old-state)
        (or (tape-element? old-symbol) (dummy? old-symbol))
        (and
         (= (length new-states) (length state-reg-names))
         (andmap new-state? new-states)
         (andmap new-datum? new-data)
         (member move '(L R N)))))))))
  (unless (state? init-state) (error 'make-TM "incorrect initial state: ~s" init-state))
  (unless (and (list? final-states) (andmap state? final-states))
   (error 'make-TM "incorrect list of final states: ~s" final-states))
  (when (keyword? dummy) (raise-argument-error 'make-TM "(not/c keyword?)" dummy))
  (when (keyword? empty) (raise-argument-error 'make-TM "(not/c keyword?)" empty))
  (when (keyword? blank) (raise-argument-error 'make-TM "(not/c keyword?)" blank))
  (when (or (equal? dummy blank) (equal? dummy empty) (equal? blank empty))
   (error 'make-TM "dummy blank and empty must be distinct, given: ~s ~s ~s" dummy blank empty))
  (unless (list? rules) (raise-argument-error 'make-TM "list of rules" rules))
  (for ((rule (in-list rules)) #:unless (rule? rule)) (error 'make-TM "incorrect rule: ~s" rule))
  (unless
   (or
    (exact-positive-integer? state-regs)
    (and (andmap keyword? state-regs) (not (check-duplicates state-regs))))
   (error 'make-TM "incorrect state-registers: ~s" state-regs))
  (unless
   (or
    (exact-positive-integer? data-regs)
    (and (andmap keyword? data-regs) (not (check-duplicates data-regs))))
   (error 'make-TM "incorrect data-registers: ~s" data-regs)))
 
 (check-arguments)

 (define (normal-rule? rule) (not (equal? (rule-old-data rule) dummy)))
 (define (empty->blank datum) (if (equal? datum empty) blank datum))
 
 (define (list->tape lst)
  (if (null? lst)
   (make-tape '() (list empty))
   (make-tape '() lst)))
  
 (define (tape->list tape)
  (remove-trailing-blanks
   (remove-heading-blanks
    (append (reverse (tape-rev-head tape)) (tape-tail tape)))))

 (define (remove-heading-blanks lst)
  (cond
   ((null? lst) '())
   ((equal? (car lst) empty) (remove-heading-blanks (cdr lst)))
   ((equal? (car lst) blank) (remove-heading-blanks (cdr lst)))
   (else lst)))
 
 (define (remove-trailing-blanks lst) (reverse (remove-heading-blanks (reverse lst))))
 
 (define (check-input input)
  (unless
   (and
    (list? input)
    (not (member empty input))
    (not (member dummy input))
    (not (ormap keyword? input)))
   (error name "incorrect input: ~s" input)))
 
 (define (check-states states)
  (unless
   (and
    (= (length states) (length state-reg-names))
    (not (ormap keyword? states))
    (not (member dummy states)))
   (error name "incorrect state-registers: ~s" states)))
 
 (define (check-data data)
  (unless
   (and
    (= (length data) (length data-reg-names))
    (not (ormap keyword? data))
    (not (member dummy data)))
   (error name "incorrect data-registers : ~s" data)))
 
 (define (check-limit x)
  (unless (or (eq? x #f) (exact-positive-integer? x))
   (error name "incorrect limit: ~s" x)))
 
 (procedure-rename TM name))

;==================================================================================================

(define (print-tape tape port mode)
 (write (list (reverse (tape-rev-head tape)) (tape-tail tape)) port))

(struct tape (rev-head tail)
 #:mutable
 #:property prop:custom-write print-tape
 #:constructor-name make-tape
 #:omit-define-syntaxes)
 
(define (make-reg-name n) (string->keyword (format "~s" n)))
(define rule-selector car)
(define rule-old-state caar)
(define rule-old-data cadar)
(define rule-instr cadr)
(define instr-new-states car)
(define instr-new-data cadr)
(define instr-move caddr)
(define line "------------------------------------------------------")

;==================================================================================================
