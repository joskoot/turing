#lang racket

(require racket "make-TM.rkt")

(define simplified-rules
'((     0         1         c         L        R        S         B
        m0        m1        mc        mL       mR       mS)
  (A   (R         R         R         R        R        -----     -----
        -----     -----     (B R)     -----    -----    -----))
  (B   (R         R         R         R        R        -----     -----
        (C0 L)    (C1 L)    -----     -----    -----    (CB L)))
  (CB  (L         L         L         L        L        -----     -----
        -----     -----     (DB c R)  -----    -----    -----))
  (C0  (L         L         L         L        L        -----     -----
        -----     -----     (D0 c R)  -----    -----    -----))
  (C1  (L         L         L         L        L        -----     -----
        -----     -----     (D1 c R)  -----    -----    -----))
  (DB  ((V L)     (E m1 L)  -----     -----    -----    -----     -----
        -----     -----     -----     -----    -----    -----))
  (D0  (R         R         (DB R)    R        R        -----     -----
        -----     -----     -----     -----    -----    -----))
  (D1  (R         R         (D0 R)    R        R        -----     -----
        -----     -----     -----     -----    -----    -----))
  (E   (L         L         (F L)     L        L        -----     -----
        -----     -----     -----     -----    -----    -----))
  (F   ((E L)     (E L)     (G L)     (E L)    (E L)    -----     -----
        -----     -----     -----     -----    -----    -----))
  (G   ((E L)     (E L)     (H R)     (E L)    (E L)    -----     -----
        -----     -----     -----     -----    -----    -----))
  (H   (-----     -----     (I R)     -----    -----    -----     -----
        -----     -----     -----     -----    -----    -----))
  (I   (-----     -----     (J mc R)  -----    -----    -----     -----
        -----     -----     -----     -----    -----    -----))
  (J   (R         R         R         R        R        -----     -----
        -----     (KL 1 R)  -----     -----    -----    -----))
  (KL  (-----     (ML m1 L) -----     (TL R)   (TR R)   -----     -----
        -----     -----     -----     -----    -----    -----))
  (ML  (L         L         L         L        L        -----     -----
        -----     -----     (NL c R)  -----    -----    -----))
  (NL  (R         R         (PL R)    R        R        -----     -----
        -----     (NR R)    -----     -----    -----    -----))
  (PL  ((NL R)    (NL R)    (SL mc R) (NL R)   (NL R)   -----     -----
        -----     (NR R)    -----     -----    -----    -----))
  (SL  (R         R         R         R        R        -----     -----
        -----     (KL 1 R)  -----     -----    -----    -----))
  (KR  (-----     (MR m1 R) -----     (TL R)   (TR R)   -----     -----
        -----     -----     -----     -----    -----    -----))
  (MR  (R         R         R         R        R        -----     -----
        -----     -----     (NR c R)  -----    -----    -----))
  (NR  (R         R         (PR R)    R        R        -----     -----
        -----     -----     -----     -----    -----    -----))
  (PR  ((NR R)    (NR R)    (SR mc L) (NR R)   (NR R)   -----     -----
        -----     -----     -----     -----    -----    -----))
  (SR  (L         L         L         L        L        -----     -----
        -----     (KR 1 R)  -----     -----    -----    -----))
  (TL  ((TL0 R)   (TL1 R)   -----     -----    -----    -----     -----
        -----     -----     -----     -----    -----    -----))
  (TR  ((TR0 R)   (TR1 R)   -----     -----    -----    -----     -----
        -----     -----     -----     -----    -----    -----))
  (TL0 (R         R         R         R        R        -----     -----
        (U 0 L)   (U 0 L)   -----     -----    -----    (U 0 L)))
  (TL1 (R         R         R         R        R        -----     -----
        (U 1 L)   (U 1 L)   R         -----    -----    (U 1 L)))
  (TR0 (R         R         R         R        R        -----     -----
        (U 0 R)   (U 0 R)   R         -----    -----    (U 0 R)))
  (TR1 (R         R         R         R        R        -----     -----
        (U 1 R)   (U 1 R)   R         -----    -----    (U 1 R)))
  (U   ((C0 m0 L) (C1 m1 L) (Uc R)    -----    -----    (CB mS L) (CB mS L)
        -----     -----     -----     -----    -----    -----))
  (Uc  ((U0 mS R) (U1 mS R) -----     -----    -----    -----     -----
        -----     -----     -----     -----    -----    -----))
  (U0  ((U0 R)    (U1 0 R)  -----     -----    -----    (UB 0 L)  (UB 0 L)
        -----     -----     -----     -----    -----    -----))
  (U1  ((U0 1 R)  (U1 R)    -----     -----    -----    (UB 1 L)  (UB 1 L)
        -----     -----     -----     -----    -----    -----))
  (UB  (L         L         -----     -----    -----    -----     -----
        -----     -----     -----     -----    -----    (CB L)))
  (V   (L         L         (W L)     L        L        -----     -----
        -----     -----     -----     -----    -----    -----))
  (W   ((V L)     (V L)     (X1 R)    (V L)    (V L)    -----     -----
        -----     -----     -----     -----    -----    -----))
  (X1  (-----     -----     (X2 R)    -----    -----    -----     -----
        -----     -----     -----     -----    -----    -----))
  (X2  ((X3 R)    -----     -----     -----    -----    -----     -----
        -----     -----     -----     -----    -----    -----))
  (X3  (-----     -----     (X4 R)    -----    -----    -----     -----
        -----     -----     -----     -----    -----    -----))
  (X4  ((X5 R)    -----     -----     -----    -----    -----     -----
        -----     -----     -----     -----    -----    -----))
  (X5  (-----     -----     (X6 R)    -----    -----    -----     -----
        -----     -----     -----     -----    -----    -----))
  (X6  ((ZR R)    -----     -----     -----    -----    -----     -----
        -----     -----     -----     -----    -----    -----))
  (ZR  (R         R         R         R        R        (ZL L)    (ZL L)
        R         R         R         R        R        (ZL S L)))
  (ZL  (L         L         (ZS S L)  -----    -----    -----     -----
        (ZL 0 L)  (ZL 1 L)  (ZS S L)  -----    -----    -----))
  (ZS  ((ZS S L)  (ZS S L)  (ZS S L)  (ZS S L) (ZS S L) (Y L)     (Y L)
        (ZS S L)  (ZS S L)  (ZS S L)  (ZS S L) (ZS S L) (Y S L)))
  ))

(define symbols (car simplified-rules))
(define rules
 (for/fold ((r '()))
  ((rule (in-list (cdr simplified-rules))))
  (define old-state (car rule))
  (define rules
   (for/list
    ((rule (in-list (cadr rule)))
     (old-symbol (in-list symbols))
     #:when (not (equal? rule '-----)))
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

(define UTM
 (make-TM
  'A '(Y) 'B 'S '_ rules #:name 'UTM))

(define input
'(c c mc
  0           c 0           c   1 1 R 0
  c c
    1 1 1 L 1 c   1 1 1 L 1 c   1 1 R 1
  c c
  1 1 1 1 R 0 c 1 1 1 1 R 0 c 1 1 1 L 1
  c c
  0           c 0           c 0
  c c c
  m1 1 1))

(define TM
 (make-TM 1 '(Y) 'B 'S '_
 '(                                ((1 1) (2 0) R)
   ((2 B) (3 1) L) ((2 0) (3 1) L) ((2 1) (2 1) R)
   ((3 B) (Y 0) R) ((3 0) (Y 0) R) ((3 1) (3 1) L))))

(UTM input #:report 'short)

(TM '(1 1 1))

(define BB
 (make-TM 1 '(Y) 'B 'S '_
 '(((1 _) (3 1) R)
   ((1 1) (1 1) R)
   ((2 _) (1 1) R)
   ((2 1) (3 1) L)
   ((3 _) (2 1) L)
   ((3 1) (Y 1) R))))

(define encoded-BB+data
'(c c mc   1 1 1 R 1 c
           1 1 1 R 1 c
               1 R 1 c c
               1 R 1 c
               1 R 1 c
           1 1 1 L 1 c c
             1 1 L 1 c
             1 1 L 1 c
         1 1 1 1 R 1 c c
         0 c 0 c 0 c c c mS))

(UTM encoded-BB+data #:report 'short)

(display "What does the original BB do?\n")

(BB '())
