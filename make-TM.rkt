#lang racket

(provide make-TM)

;===================================================================================================

(define
 (make-TM
  init-state final-states
  blank space dummy
  rules
  #:registers (registers 2)
  #:name (name 'TM-without-name))

 ; First check the registers argument.
 ; The register-names and the nr-of-registers are required for checking the rules.

 (define register-names
  (cond
   ((and (exact-positive-integer? registers) (> registers 1))
    (for/list ((k (in-range registers))) (string->keyword (format "~s" k))))
   ((and
     (list? registers)
     (> (length registers) 1)
     (andmap keyword? registers)
     (not (check-duplicates registers)))
    registers)
   (else (error 'make-TM "incorrect registers argument: ~s" registers))))

 (define nr-of-registers (length register-names))
 
 (check-make-TM-arguments
  init-state
  final-states
  blank
  space
  dummy
  rules
  nr-of-registers
  register-names
  name)
  
 (define
  (TM
   input
   #:registers (register-values #f)
   #:report (report #f)
   #:limit (limit #f))
  
  (check-TM-arguments input register-values report limit)
  
  (define (TM-proper move-nr register-hash tape)
   (define old-state (hash-ref register-hash state-register-name))
    (cond
     ((set-member? set-of-final-states old-state)
      (values (sub1 move-nr) (hash-ref register-hash state-register-name) tape))
     (else
      (when (and limit (> move-nr limit))
       (error name "About to exceed max nr of ~s moves~nregisters: ~s~ntape: ~s" limit
        (for/list ((reg (in-list register-names))) (hash-ref register-hash reg))
         tape))
      (define current-tape-datum (car (tape-tail tape)))
      (hash-set! register-hash bus-register-name current-tape-datum)
      (define rule (find-rule old-state current-tape-datum))
      (define new-state (rule-new-state rule))
      (define new-datum
       (let ((new-datum (rule-new-datum rule)))
        (cond
         ((dummy? new-datum) current-tape-datum)
         ((keyword? new-datum) (hash-ref register-hash new-datum))
         (else new-datum))))
      (define old-registers
       (cons old-state
        (cons current-tape-datum
         (for/list ((register-name (in-list (cddr register-names))))
          (hash-ref register-hash register-name)))))
      (define new-registers
       (cons new-state
        (cons new-datum
         (for/list ((new-register (in-list (cddr (rule-registers rule))))
                    (register-name (in-list (cddr register-names))))
          (cond
           ((dummy? new-register) (hash-ref register-hash register-name))
           ((keyword? new-register) (hash-ref register-hash new-register))
           (else new-register))))))
      (define new-register-hash (make-hash (map cons register-names new-registers)))
      (define new-tape-datum (hash-ref new-register-hash bus-register-name))
      (define new-tape
       (case (rule-move rule)
        ((R) (move-right tape new-tape-datum))
        ((L) (move-left tape new-tape-datum))
        ((N) (no-move tape new-tape-datum))))
      (case report
       ((#t long)
        (printf "move-nr  : ~s~n" move-nr)
        (printf "rule     : ~s~n" rule)
        (printf "registers: ~s -> ~s~n" old-registers new-registers)
        (printf "new tape : ~s~n" new-tape)
        (print-line))
       ((short) (printf "~s, ~s -> ~s, ~s~n" move-nr old-state new-state new-tape)))
      (TM-proper (add1 move-nr) new-register-hash new-tape))))
  
  (define initial-tape (make-tape '() (if (null? input) (list blank) input)))
  
  (define register-hash
   (cond
    ((list? register-values)
     (make-hash (map cons register-names register-values)))
    (else
     (make-hash
      (cons (cons state-register-name init-state)
       (map fill-blank (cdr register-names)))))))
  
  (when report
   (print-line)
   (printf "Report of ~s~n" name)
   (printf "Initial tape: ~s~n" initial-tape)
   (print-line))
   (define-values (nr-of-moves final-state tape) (TM-proper 1 register-hash initial-tape))
   (when (eq? report 'short) (print-line))
   (when report (printf "End of report of ~s~n" name) (print-line))
   (values nr-of-moves final-state (remove-blank-spaces tape)))

 (define state-register-name (car register-names))
 (define bus-register-name (cadr register-names))
 (define set-of-final-states (apply set final-states))
 (define (dummy? x) (equal? x dummy))
 
 (define-values (normal-rule-hash dummy-rule-hash)
  (for/fold ((normal-hash (hash)) (dummy-hash (hash))) ((rule (in-list rules)))
   (define old-state (rule-old-state rule))
   (define old-datum (rule-old-datum rule))
   (if (dummy? old-datum)
    (values normal-hash (hash-set dummy-hash old-state rule))
    (values (hash-set normal-hash (car rule) rule) dummy-hash))))
 
 (define (find-rule old-state current-tape-datum)
  (define (find-rule-error)
   (error name "no rule with old-state: ~s and old-datum: ~s" old-state current-tape-datum))
  (define (find-dummy-rule) (hash-ref dummy-rule-hash old-state find-rule-error))
  (hash-ref normal-rule-hash (list old-state current-tape-datum) find-dummy-rule))
 
 (define (check-TM-arguments input register-values report limit)
  (unless (list? input) (raise-argument-error name "list of tape-symbols" input))
  (when (ormap dummy? input) (error name "dummy not allowed in input: ~s" input))
  (when (member blank input) (error name "blank not allowed in input: ~s" input))
  (cond
   ((list? register-values)
    (unless (list? register-values)
     (raise-argument-error name "list of register values" register-values))
    (when (ormap dummy? register-values)
     (error name "dummy not allowed as register-value: ~s" register-values))
    (when (ormap keyword? register-values)
     (error name "keywords not allowed as register-values: ~s" register-values))
    (unless (= (length register-values) nr-of-registers)
     (error name "~s register-values required, given ~s in: ~s"
      nr-of-registers (length register-values) register-values)))
   (register-values (error name "incorrect register-values: ~s" register-values)))
  (unless (member report '(#f #t short long))
   (error name "report must be #f, #t, short or long, given ~s" report))
  (unless (or (not limit) (exact-positive-integer? limit))
   (raise-argument-error name "(or/c #f exact-positive-number?)" limit)))

 (define (fill-blank register-name) (cons register-name blank))

 (define (remove-blank-spaces tape)
  (define content (append (reverse (tape-reversed-head tape)) (tape-tail tape)))
  (define (remove-heading-spaces content)
  (cond
   ((null? content) '())
   ((equal? (car content) blank) (remove-heading-spaces (cdr content)))
   ((equal? (car content) space) (remove-heading-spaces (cdr content)))
   (else content)))
  (reverse (remove-heading-spaces (reverse (remove-heading-spaces content)))))

 (define (move-left tape d)
  (define datum (if (equal? d blank) space d))
  (define reversed-head (tape-reversed-head tape))
  (define tail (cons datum (cdr (tape-tail tape))))
  (cond
   ((null? reversed-head) (make-tape '() (cons blank tail)))
   (else (make-tape (cdr reversed-head) (cons (car reversed-head) tail)))))
      
 (define (move-right tape d)
  (define datum (if (equal? d blank) space d))
  (define reverse-head (tape-reversed-head tape))
  (define tail (cons datum (cdr (tape-tail tape))))
  (cond
   ((null? (cdr tail)) (make-tape (cons (car tail) reverse-head) (list blank)))
   (else (make-tape (cons (car tail) reverse-head) (cdr tail)))))

 (define (no-move tape d)
 (define datum (if (equal? d blank) space d))
  (make-tape (tape-reversed-head tape) (cons datum (cdr (tape-tail tape)))))

 (procedure-rename TM name))

;===================================================================================================

(define (print-tape tape port mode)
 (write (list (reverse (tape-reversed-head tape)) (tape-tail tape)) port))

; print-tape must be defined before struct tape.

(struct tape (reversed-head tail)
 #:property prop:custom-write print-tape
 #:constructor-name make-tape
 #:omit-define-syntaxes)

(define rule-old-state caar)
(define rule-old-datum cadar)
(define rule-registers cadr)
(define (rule-new-state rule) (car (rule-registers rule)))
(define (rule-new-datum rule) (cadr (rule-registers rule)))
(define rule-move caddr)

(define
 (check-make-TM-arguments
  init-state final-states blank space dummy rules nr-of-registers register-names name)
 (when (keyword? blank) (error 'make-TM "incorrect blank: ~s" blank))
 (when (keyword? space) (error 'make-TM "incorrect space: ~s" space))
 (when (keyword? dummy) (error 'make-TM "incorrect dummy: ~s" dummy))
 (when (check-duplicates (map list (list blank space dummy)))
  (error 'make-TM "blank, space and dummy must be distinct, given ~s, ~s and ~s"
   blank space dummy))
 (when (keyword? init-state)
  (error 'make-TM "init-state must not be a keyword, given: ~s" init-state))
 (when (equal? init-state dummy)
  (error 'make-TM "init-state must not equal the dummy: ~s" init-state))
 (unless
  (and
   (list? final-states)
   (not (ormap keyword? final-states))
   (not (for/or ((final-state (in-list final-states))) (equal? final-state dummy))))
  (error 'make-TM "incorrect argument for final-states: ~s" final-states))
 (define set-of-final-states (apply set final-states))
 (define (rule? rule)
  (and
   (list? rule)
   (= (length rule) 3)
   (list? (car rule))
   (= (length (car rule)) 2)
   (list? (cadr rule))
   (= (length (cadr rule)) nr-of-registers)
   (member (rule-move rule) '(N R L))
   (let
    ((old-state (rule-old-state rule))
     (old-datum (rule-old-datum rule))
     (rule-registers (rule-registers rule)))
    (and
     (not (set-member? set-of-final-states old-state))
     (not (keyword? old-state))
     (not (equal? old-state dummy))
     (not (keyword? old-datum))
     (andmap new-value? rule-registers)))))
 (define (new-value? x) (or (member x register-names) (not (keyword? x))))
 (unless (list? rules) (raise-argument-error 'make-TM "list of rules" rules))
 (for ((rule (in-list rules)))
  (unless (rule? rule) (error 'make-TM "incorrect rule: ~s" rule)))
 (let ((duplicate (check-duplicates rules #:key car)))
  (when duplicate (error 'make-TM "duplicate rule selector: ~s" duplicate))))
 
(define (print-line) (printf "-------------------------------------------------------------~n"))

;===================================================================================================
