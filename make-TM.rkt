#lang racket

(provide make-TM)

(define (make-TM
         init-state
         final-states
         empty blank dummy
         rules
         #:state-registers (state-regs 1)
         #:data-registers (sym-regs 1)
         #:name (name 'TM-without-name))

 (define (make-reg-name n) (string->keyword (format "~s" n)))

 (define state-reg-names
  (if (exact-positive-integer? state-regs)
   (build-list state-regs make-reg-name)
   state-regs))
 
 (define sym-reg-names
  (if (exact-positive-integer? sym-regs)
   (build-list sym-regs make-reg-name)
   sym-regs))

 (define tape #f)
 (define limit? #f)
 (define report #f)
 (define state-reg-hash #f)
 (define sym-reg-hash #f)
 (define move-counter #f)
 (define rule-selector car)
 (define rule-old-state caar)
 (define rule-old-sym cadar)
 (define rule-instr cadr)
 (define instr-new-states car)
 (define instr-new-syms cadr)
 (define instr-move caddr)
 (define (normal-rule? rule) (not (equal? (rule-old-sym rule) dummy)))
 (define (empty->blank sym) (if (equal? sym empty) blank sym))
 (define line "------------------------------------------------------")
 (define (get-state state) (if (keyword? state) (hash-ref state-reg-hash state) state))
 (define (get-sym sym) (if (keyword? sym) (hash-ref sym-reg-hash sym) sym))
 
 (define (get-state* state reg)
  (cond
   ((keyword? state) (hash-ref state-reg-hash state))
   ((equal? state dummy) (hash-ref state-reg-hash reg))
   (else state)))
 
 (define (get-sym* sym reg)
  (cond
   ((keyword? sym) (hash-ref sym-reg-hash sym))
   ((equal? sym dummy) (hash-ref sym-reg-hash reg))
   (else sym)))
 
 (define (check-arguments) #t)

 (check-arguments)

 (define (print-tape tape port mode)
  (write (list (reverse (tape-rev-head tape)) (tape-tail tape)) port))

 (struct tape (rev-head tail)
  #:mutable
  #:property prop:custom-write print-tape
  #:constructor-name make-tape
  #:omit-define-syntaxes)

 (define state-reg (car state-reg-names))
 (define databus (car sym-reg-names))
 (define (tape-read) (car (tape-tail tape)))
 (define (tape-write sym) (set-tape-tail! tape (cons (empty->blank sym) (cdr (tape-tail tape)))))
 (define final-states-set (apply set final-states))
 (define state-reg-hash* (make-hasheq (map (λ (x) (cons x init-state)) state-reg-names)))
 (define sym-reg-hash* (make-hasheq (map (λ (x) (cons x empty)) sym-reg-names)))
 
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

 (define (rule-error* old-state sym old-states old-syms)
  (error name
   "~nNo rule for state ~s and tape-element ~s~n~
    move: ~s~n~
    tape: ~s~n~
    state-registers: ~s~n~
    data-registers: ~s~n"
   old-state sym
   move-counter
   tape
   old-states
   old-syms))

 (define (TM-proper)
  (define old-state (hash-ref state-reg-hash state-reg))
  (cond
   ((set-member? final-states-set old-state) old-state)
   ((and limit? (>= move-counter limit?))
    (error name
     "~nAbout to exceed the max nr of moves:~n~
      move: ~s~n~
      tape: ~s~n~
      state-registers: ~s~n~
      data-registers: ~s~n"
     move-counter
     tape
     (map get-state state-reg-names)
     (map get-sym sym-reg-names)))
   (else
    (define sym (tape-read))
    (hash-set! sym-reg-hash databus sym)
    (define old-states (map get-state state-reg-names))
    (define old-syms (map get-sym sym-reg-names))
    (set! move-counter (add1 move-counter))
    (define (rule-error) (rule-error* old-state sym old-states old-syms))
    (define (get-dummy-rule) (hash-ref dummy-rules-hash old-state rule-error))
    (define rule (hash-ref normal-rules-hash (list old-state sym) get-dummy-rule))
    (define instr (rule-instr rule))
    (define new-states (map get-state* (instr-new-states instr) state-reg-names))
    (define new-syms (map get-sym* (instr-new-syms instr) sym-reg-names))
    (define new-state (car new-states))
    (define move (instr-move instr))
    (set! state-reg-hash (make-hash (map cons state-reg-names new-states)))
    (set! sym-reg-hash (make-hash (map cons sym-reg-names new-syms)))
    (define new-sym (car new-syms))
    (tape-write new-sym)
    (case move
     ((L) (move-left))
     ((R) (move-right))
     (else (void)))
    (when report
     (printf
      (string-append
       "move            : ~s~n"
       "rule            : ~s~n"
       "state registers : ~s -> ~s~n"
       "data registers  : ~s -> ~s~n"
       "move            : ~s~n"
       "new tape content: ~s~n"
       "~a~n")
      move-counter
      rule
      old-states new-states
      old-syms new-syms
      move
      tape
      line))
    (TM-proper))))

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
 (define (check-input input) #t)
 (define (check-states states) #t)
 (define (check-syms syms) #t)
 (define (check-limit x) #t)

 (define
  (TM
   input
   #:state-registers (states #f)
   #:data-registers (syms #f)
   #:report (report? #f)
   #:limit (limit #f))
  (check-input input)
  (check-limit limit)
  (when states (check-states states))
  (when syms (check-syms syms))
  (set! limit? limit)
  (set! report (and report? #t))
  (set! move-counter 0)
  (set! tape (list->tape input))
  (set! state-reg-hash
   (if states
    (make-hash (map cons state-reg-names states))
    (hash-copy state-reg-hash*)))
  (set! sym-reg-hash
   (if syms
    (make-hash (map cons sym-reg-names syms))
    (hash-copy sym-reg-hash*)))
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
    (map get-sym sym-reg-names)
    line))
  (define final-state (TM-proper))
  (when report (printf "~s halted in final state ~s~nEnd of report.~n~a~n" name final-state line))
  (define tape* (tape->list tape))
  (set! tape #f)
  (set! sym-reg-hash #f)
  (set! state-reg-hash #f)
  (set! report #f)
  (values move-counter final-state tape*))

 (procedure-rename TM name))

