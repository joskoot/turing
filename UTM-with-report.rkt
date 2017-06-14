#lang racket

(require racket "make-TM.rkt")
;(code:line)
;(code:comment "Universal Turing Machine")
;(code:comment "Copied from “Formal Languages and their Relation to Automata”,")
;(code:comment "Addison-Wesley, 1969, p 105-107 (ISBN 0-201-0298 3-9)")
;(code:comment "I have replaced the entries in column mc")
;(code:comment "and rows TL0, TL1, TR0 and TR1 by an R.")
;(code:comment "In the book these are underscores, but that does not work.")
;(code:line)
(define simplified-rules
;(code:comment "The tape-symbols:")
'((     0         1         c         L        R        S         B
        m0        m1        mc        mL       mR       mS)
;(code:comment "The rules (states in the first column)")
;(code:comment "R = (_ _ R), L = (_ _ L), N = (_ _ N)")
;(code:comment "stop and error are final states.")
;(code:comment "(new-state move) leaves the current symbol as it is.")
;(code:comment "(new-state new-symbol move) obvious.")
;(code:comment "")
;(code:comment "First find the current element of the data.")
  (A   (R         R         R         R        R        stop      stop
        stop      stop      (B R)     stop     stop     stop))
  (B   (R         R         R         R        R        stop      stop
        (C0 L)    (C1 L)    stop      stop     stop     (CB L)))
;(code:comment "Find the block of the current state.")
  (CB  (L         L         L         L        L        stop      stop
        stop      stop      (DB c R)  stop     stop     stop))
  (C0  (L         L         L         L        L        stop      stop
        stop      stop      (D0 c R)  stop     stop     stop))
  (C1  (L         L         L         L        L        stop      stop
        stop      stop      (D1 c R)  stop     stop     stop))
;(code:comment "Find the sub-block corresponding to the current datum.")
  (DB  ((V N)     (E m1 L)  stop      stop     stop     stop      stop
        error     error     error     error    error    error))
  (D0  (R         R         (DB R)    R        R        stop      stop
        error     error     error     error    error    error))
  (D1  (R         R         (D0 R)    R        R        stop      stop
        error     error     error     error    error    error))
;(code:comment "Rewind to start of current block.")
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
;(code:comment "Locate next state in current block.")
  (J   (R         R         R         R        R        stop      stop
        stop      (KL 1 R)  stop      stop     stop     stop))
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
;(code:comment "Record symbol to be written.")
  (TL  ((TL0 R)   (TL1 R)   stop      stop     stop     stop      stop
        error     error     error     error    error    error))
  (TR  ((TR0 R)   (TR1 R)   stop      stop     stop     stop      stop
        error     error     error     error    error    error))
;(code:comment "Find the cell in which to write the new symbol.")
  (TL0 (R         R         R         R        R        stop      stop
        (U 0 L)   (U 0 L)   stop      stop     stop     (U 0 L)))
  (TL1 (R         R         R         R        R        stop      stop
        (U 1 L)   (U 1 L)   R         stop     stop     (U 1 L)))
  (TR0 (R         R         R         R        R        stop      stop
        (U 0 R)   (U 0 R)   R         stop     stop     (U 0 R)))
  (TR1 (R         R         R         R        R        stop      stop
        (U 1 R)   (U 1 R)   R         stop     stop     (U 1 R)))
;(code:comment "Do we have a final state?")
  (U   ((C0 m0 L) (C1 m1 L) stop      stop     stop     (CB mS L) (CB mS L)
        error     error     error     error    error    error))
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
;(code:comment "We have a final state. Erase all at the left of the data.")
  (ZR  (R         R         R         R        R        (ZL L)    (ZL L)
        R         R         R         R        R        (ZL B L)))
  (ZL  (L         L         (ZB B L)  error    error    error     error
        (ZL 0 L)  (ZL 1 L)  (ZB B L)  error    error    error))
  (ZB  ((ZB B L)  (ZB B L)  (ZB B L)  (ZB B L) (ZB B L) (Y B N)   (Y B N)
        (ZB B L)  (ZB B L)  (ZB B L)  (ZB B L) (ZB B L) (Y B N)))
  ))
;(code:line)
(define symbols (car simplified-rules))
;(code:line)
(define rules
 (for/fold ((r '()))
  ((rule (in-list (cdr simplified-rules))))
  (define old-state (car rule))
  (define rules
   (for/list ((rule (in-list (cadr rule))) (old-symbol (in-list symbols)))
    (case rule
     ((R)     (list (list old-state old-symbol) (list old-state old-symbol) 'R))
     ((L)     (list (list old-state old-symbol) (list old-state old-symbol) 'L))
     ((stop)  (list (list old-state old-symbol) (list 'stop     old-symbol) 'N))
     ((error) (list (list old-state old-symbol) (list 'error    old-symbol) 'N))
     (else
      (define-values (new-state new-symbol move) 
       (cond
        ((= (length rule) 2) (values (car rule) old-symbol (cadr rule))) 
        (else (apply values rule))))
      (list (list old-state old-symbol) (list new-state new-symbol) move)))))
  (append r rules)))
;(code:line)
;(pretty-print rules)
;(code:line)
(define UTM
 (make-TM
  'A '(stop error Y) 'B 'S '_ rules #:name 'UTM))
;(code:line)
;(code:comment "The following program puts a 0 in front of the data m1 1 1.")
(define input
;(code:comment "The encoded program.")
'(c c mc
;(code:comment "B           0             1")
;(code:comment "State 1.")
  0           c 0           c   1 1 R 0
  c c
;(code:comment "State 2.")
    1 1 1 L 1 c   1 1 1 L 1 c   1 1 R 1
  c c
;(code:comment "State 3.")
  1 1 1 1 R 0 c 1 1 1 1 R 0 c 1 1 1 L 1
  c c
;(code:comment "State 4.")
  0           c 0           c 0
  c c c
;(code:comment "The data.")
  m1 1 1))
;(code:line)
;(code:comment "The above program is an encoding of:")
(define TM
 (make-TM 1 '(Y) 'B 'S '_
 '(((1 1) (2 0) R)
   ((2 B) (3 1) L) ((2 0) (3 1) L) ((2 1) (2 1) R)
   ((3 B) (Y 0) R) ((3 0) (Y 0) R) ((3 1) (3 1) L))))
;(code:line)
;(code:comment "which produces:")
;(code:line)
(TM '(1 1 1))
;(code:line)
;(code:comment "Now let's check that the UTM produces the same")
;(code:comment "given the above encoding and data.")
;(code:line)
(UTM input #:report 'short)