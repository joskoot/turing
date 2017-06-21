#lang racket

(require racket "make-TM.rkt")
;codeline)
;codecomment "Universal Turing Machine")
;codecomment "Copied from “Formal Languages and their Relation to Automata”,")
;codecomment "Addison-Wesley, 1969, p 105-107 (ISBN 0-201-0298 3-9)")
;codecomment "I have replaced the entries in column mc")
;codecomment "and rows TL0, TL1, TR0 and TR1 by an R.")
;codecomment "In the book these are underscores, but that does not work.")
;(code:line)
(define simplified-rules
;codecomment "The tape-symbols:")
'((     0         1         c         L        R        S         B
        m0        m1        mc        mL       mR       mS)
;codecomment "The rules (states in the first column)")
;codecomment "R = (_ _ R), L = (_ _ L)")
;codecomment "stop and error are erroneous final states.")
;codecomment "(new-state move) = (new-state _ move).")
;codecomment "(new-state new-symbol move) obvious.")
;codecomment "")
;codecomment "First find the current element of the data.")
  (A   (R         R         R         R        R        stop      stop
        stop      stop      (B R)     stop     stop     stop))
  (B   (R         R         R         R        R        stop      stop
        (C0 L)    (C1 L)    stop      stop     stop     (CB L)))
;codecomment "Find the block of the current state.")
  (CB  (L         L         L         L        L        stop      stop
        stop      stop      (DB c R)  stop     stop     stop))
  (C0  (L         L         L         L        L        stop      stop
        stop      stop      (D0 c R)  stop     stop     stop))
  (C1  (L         L         L         L        L        stop      stop
        stop      stop      (D1 c R)  stop     stop     stop))
;codecomment "Find the sub-block corresponding to the current datum.")
  (DB  ((V L)     (E m1 L)  stop      stop     stop     stop      stop
        error     error     error     error    error    error))
  (D0  (R         R         (DB R)    R        R        stop      stop
        error     error     error     error    error    error))
  (D1  (R         R         (D0 R)    R        R        stop      stop
        error     error     error     error    error    error))
;codecomment "Rewind to start of program and mark first block.")
;codecomment "Id est find the 3 starting c-s and mark the third one.")
;codecomment "This is marker m2.")
;codecomment "Let m1 be the marker of the current sub-block.")
;codecomment "The distinction between m1 and m2 has been copied from")
;codecomment "Formal Languages and their Relation to Automata, Hopcroft and Ullman.")
  (E   (L         L         (F L)     L        L        stop      stop
        error     error     error     error    error    error))
  (F   ((E L)     (E L)     (G L)     (E L)    (E L)    stop      stop
        error     error     error     error    error    error))
  (G   ((E L)     (E L)     (H R)     (E L)    (E L)    stop      stop
        error     error     error     error    error    error))
  (H   (stop      stop      (I R)     stop     stop     stop      stop
        error     error     error     error    error    error))
  (I   (stop      stop      (J mc R)  stop     stop     stop      stop
        error     error     error     error    error    error))
;codecomment "Locate next state.")
  (J   (R         R         R         R        R        stop      stop
        stop      (KL 1 R)  stop      stop     stop     stop))
;codecomment "For each remaining 1 of next state shift marker m2 to next block")
;codecomment "and shift marker m1 one to the right until no 1-s remain.")
;codecomment "When done go to the block marked with m2")
;codecomment "find the instruction corresponding to the current tape-symbol")
;codecomment "and execute the instruction (TR0, TR1, TL0, or TL1)")
  (KL  (stop      (ML m1 L) stop      (TL R)   (TR R)   stop      stop
        error     error     error     error    error    error))
  (ML  (L         L         L         L        L        stop      stop
        stop      stop      (NL c R)  stop     stop     stop))
  (NL  (R         R         (PL R)    R        R        stop      stop
        stop      (NR R)    stop      stop     stop     stop))
  (PL  ((NL R)    (NL R)    (SL mc R) (NL R)   (NL R)   stop      stop
        stop      (NR R)    stop      stop     stop     stop))
  (SL  (R         R         R         R        R        stop      stop
        stop      (KL 1 R)  stop      stop     stop     stop))
  (KR  (stop      (MR m1 R) stop      (TL R)   (TR R)   stop      stop
        error     error     error     error    error    error))
  (MR  (R         R         R         R        R        stop      stop
        stop      stop      (NL c R)  stop     stop     stop))
  (NR  (R         R         (PR R)    R        R        stop      stop
        error     error     error     error    error    error))
  (PR  ((NR R)    (NR R)    (SR mc L) (NR R)   (NR R)   stop      stop
        error     error     error     error    error    error))
  (SR  (L         L         L         L        L        stop      stop
        stop      (KR 1 R)  stop      stop     stop     stop))
;codecomment "Record symbol to be written.")
  (TL  ((TL0 R)   (TL1 R)   stop      stop     stop     stop      stop
        error     error     error     error    error    error))
  (TR  ((TR0 R)   (TR1 R)   stop      stop     stop     stop      stop
        error     error     error     error    error    error))
;codecomment "Find marker in data region and write the new symbol.")
  (TL0 (R         R         R         R        R        stop      stop
        (U 0 L)   (U 0 L)   stop      stop     stop     (U 0 L)))
  (TL1 (R         R         R         R        R        stop      stop
        (U 1 L)   (U 1 L)   R         stop     stop     (U 1 L)))
  (TR0 (R         R         R         R        R        stop      stop
        (U 0 R)   (U 0 R)   R         stop     stop     (U 0 R)))
  (TR1 (R         R         R         R        R        stop      stop
        (U 1 R)   (U 1 R)   R         stop     stop     (U 1 R)))
;codecomment "Adjust the marker,")
  (U   ((C0 m0 L) (C1 m1 L) stop      stop     stop     (CB mS L) (CB mS L)
        error     error     error     error    error    error))
;codecomment "No new rule found (zero encountered in state DB)")
;codecomment "Check that we have a final state.")
  (V   (L         L         (W L)     L        L        stop      stop
        error     error     error     error    error    error))
  (W   ((V L)     (V L)     (X1 R)    (V L)    (V L)    stop      stop
        error     error     error     error    error    error))
  (X1  (stop      stop      (X2 R)    stop     stop     stop      stop
        error     error     error     error    error    error))
  (X2  ((X3 R)    stop      stop      stop     stop     stop      stop
        error     error     error     error    error    error))
  (X3  (stop      stop      (X4 R)    stop     stop     stop      stop
        error     error     error     error    error    error))
  (X4  ((X5 R)    stop      stop      stop     stop     stop      stop
        error     error     error     error    error    error))
  (X5  (stop      stop      (X6 R)    stop     stop     stop      stop
        error     error     error     error    error    error))
  (X6  ((ZR R)    stop      stop      stop     stop     stop      stop
        error     error     error     error    error    error))
;codecomment "We have a final state. Erase all at the left of the data.")
  (ZR  (R         R         R         R        R        (ZL L)    (ZL L)
        R         R         R         R        R        (ZL S L)))
  (ZL  (L         L         (ZS S L)  error    error    error     error
        (ZL 0 L)  (ZL 1 L)  (ZS S L)  error    error    error))
  (ZS  ((ZS S L)  (ZS S L)  (ZS S L)  (ZS S L) (ZS S L) (Y L)     (Y L)
        (ZS S L)  (ZS S L)  (ZS S L)  (ZS S L) (ZS S L) (Y S L)))
  ))
;codeline)
(define symbols (car simplified-rules))
;codeline)
(define rules
 (for/fold ((r '()))
  ((rule (in-list (cdr simplified-rules))))
  (define old-state (car rule))
  (define rules
   (for/list
    ((rule (in-list (cadr rule)))
     (old-symbol (in-list symbols))
     #:when (not (or (equal? rule 'stop) (equal? rule 'error))))
    (case rule
     ((R)     (list (list old-state old-symbol) (list old-state old-symbol) 'R))
     ((L)     (list (list old-state old-symbol) (list old-state old-symbol) 'L))
     (else
      (define-values (new-state new-symbol move) 
       (cond
        ((= (length rule) 2) (values (car rule) old-symbol (cadr rule))) 
        (else (apply values rule))))
      (list (list old-state old-symbol) (list new-state new-symbol) move)))))
  (append r rules)))
;codeline)
;(pretty-print rules)
;codeline)
(define UTM
 (make-TM
  'A '(stop error Y) 'B 'S '_ rules #:name 'UTM))
;codeline)
;codecomment "The following program puts a 0 in front of the data m1 1 1.")
(define input
;codecomment "The encoded program.")
'(c c mc
;codecomment "B           0             1")
;codecomment "State 1.")
  0           c 0           c   1 1 R 0
  c c
;codecomment "State 2.")
    1 1 1 L 1 c   1 1 1 L 1 c   1 1 R 1
  c c
;codecomment "State 3.")
  1 1 1 1 R 0 c 1 1 1 1 R 0 c 1 1 1 L 1
  c c
;codecomment "State 4.")
  0           c 0           c 0
  c c c
;codecomment "The data.")
  m1 1 1))
;codeline)
;codecomment "The above program is an encoding of:")
(define TM
 (make-TM 1 '(Y) 'B 'S '_
 '(((1 1) (2 0) R)
   ((2 B) (3 1) L) ((2 0) (3 1) L) ((2 1) (2 1) R)
   ((3 B) (Y 0) R) ((3 0) (Y 0) R) ((3 1) (3 1) L))))
;codeline)
;codecomment "which produces:")
;codeline)
(TM '(1 1 1))
;codeline)
;codecomment "Now let's check that the UTM produces the same")
;codecomment "given the above encoding and data.")
;codeline)
(UTM input #:report 'short)