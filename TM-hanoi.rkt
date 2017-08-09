#lang racket
(require "make-TM.rkt")

#|
The Tower of Hanoi

An instruction to move a tower of n disks is denoted as (tower ‹f› ‹t› ‹r› 1 ...+)
where the number of ones is the number of disks.
‹f› is the startig peg, ‹t› the peg of destination and ‹r› the third peg.
An instruction to move a disk is denoted as (move ‹f› ‹t› ‹r› 1 ...+)
where the number of ones identifies the disk to be moved.
A disk with more ones is larger than a disk with less ones.
(instruction (tower ‹f› ‹t› ‹r› 1) is immediately replaced by
instruction (move ‹f› ‹t› ‹r› 1)
(instruction (tower ‹f› ‹t› ‹r› 1 1 ...+) is replaced by
(tower ‹f› ‹r› ‹t› 1 ...+ move ‹f› ‹t› ‹r› 1 1 ...+ tower ‹r› ‹f› ‹r› 1 ...+).
Tower-instructions are processed until no more of them remain.

The following registers are used:
#:state  : the primary state
#:bus    : the input/output-register
#:prev   : previous tape-symbol during insertion of a tape-symbol.
#:arg    : tape-symbol to be inserted.
#:return : primary state to be assumed after insertion is complete.
#:peg1   : starting peg.
#:peg1   : destination peg.
#:peg1   : third peg.
|#

(define registers
                   '(#:state  #:bus     #:prev   #:return #:arg    #:peg1   #:peg2   #:peg3  ))

(define rules
'(((start    tower) (getpegs1 move      _        _        _        _        _        _       ) R)
  ((start    blank) (halt     _         _        _        _        _        _        _       ) N)
  ((start    space) (halt     _         _        _        _        _        _        _       ) N)
  ((start    _    ) (start    _         _        _        _        _        _        _       ) R)

  ((getpegs1 _    ) (getpegs2 _         _        _        _        #:bus    _        _       ) R)
  ((getpegs2 _    ) (getpegs3 _         _        _        _        _        #:bus    _       ) R)
  ((getpegs3 _    ) (right1   _         _        _        _        _        _        #:bus   ) R)
  
  ((right1   1    ) (right2   _         _        _        _        _        _        _       ) R)
  ((right2   1    ) (right3   m1        _        _        _        _        _        _       ) R)
  ((right2   _    ) (rewind   _         _        _        _        _        _        _       ) L)
  ((right3   1    ) (_        _         _        _        _        _        _        _       ) R)
  ((right3   _    ) (insert   _         _        right4   tower    _        _        _       ) N)
  ((right4   _    ) (right5   _         _        _        _        _        _        _       ) R)
  ((right5   _    ) (insert   _         _        right6   #:peg3   _        _        _       ) N)
  ((right6   _    ) (right7   _         _        _        _        _        _        _       ) R)
  ((right7   _    ) (insert   _         _        right8   #:peg2   _        _        _       ) N)
  ((right8   _    ) (right9   _         _        _        _        _        _        _       ) R)
  ((right9   _    ) (insert   _         _        right10  #:peg1   _        _        _       ) N)
  ((right10  _    ) (right11  _         _        _        _        _        _        _       ) R)
  ((right11  _    ) (insert   _         _        right12  1        _        _        _       ) N)
  ((right12  m1   ) (right13  1         _        _        _        _        _        _       ) R)
  ((right12  _    ) (_        _         _        _        _        _        _        _       ) L)
  ((right13  tower) (left     _         _        _        _        _        _        _       ) R)
  ((right13  1    ) (right14  m1        _        _        _        _        _        _       ) R)
  ((right14  1    ) (right14  _         _        _        _        _        _        _       ) R)
  ((right14  tower) (right15  _         _        _        _        _        _        _       ) R)
  ((right15  _    ) (right16  _         _        _        _        _        _        _       ) R)
  ((right16  _    ) (right17  _         _        _        _        _        _        _       ) R)
  ((right17  _    ) (right18  _         _        _        _        _        _        _       ) R)
  ((right18  _    ) (insert   _         _        right19  1        _        _        _       ) N)
  ((right19  m1   ) (right20  1         _        _        _        _        _        _       ) R)
  ((right19  _    ) (right19  _         _        _        _        _        _        _       ) L)
  ((right20  1    ) (right14  m1        _        _        _        _        _        _       ) R)
  ((right20  tower) (left     _         _        _        _        _        _        _       ) L)

  ((left     _    ) (_        _         _        _        _        _        _        _       ) L)
  ((left     move ) (left1    _         _        _        _        _        _        _       ) N)
  ((left1    _    ) (insert   _         _        left2    #:peg2   _        _        _       ) N)
  ((left2    _    ) (insert   _         _        left3    #:peg3   _        _        _       ) N)
  ((left3    _    ) (insert   _         _        left4    #:peg1   _        _        _       ) N)
  ((left4    _    ) (insert   _         _        left5    tower    _        _        _       ) N)
  ((left5    _    ) (left5    _         _        _        _        _        _        _       ) R)
  ((left5    1    ) (left6    _         _        _        _        _        _        _       ) R)
  ((left6    1    ) (left7    m1        _        _        _        _        _        _       ) L)
  ((left6    _    ) (rewind   _         _        _        _        _        _        _       ) L)
  ((left7    _    ) (left7    _         _        _        _        _        _        _       ) L)
  ((left7    move ) (left8    _         _        _        _        _        _        _       ) N)
  ((left8    move ) (insert   _         _        left9    1        _        _        _       ) N)
  ((left9    m1   ) (left10   1         _        _        _        _        _        _       ) R)
  ((left9    _    ) (_        _         _        _        _        _        _        _       ) R)
  ((left10   1    ) (left11   m1        _        _        _        _        _        _       ) L)
  ((left10   _    ) (rewind   _         _        _        _        _        _        _       ) L)
  ((left11   move ) (insert   _         _        left9    1        _        _        _       ) N)
  ((left11   _    ) (_        _         _        _        _        _        _        _       ) L)

  ((rewind   blank) (start    _         _        _        _        _        _        _       ) R)
  ((rewind   space) (start    _         _        _        _        _        _        _       ) R)
  ((rewind   _    ) (rewind   _         _        _        _        _        _        _       ) L)

  ((insert   _    ) (insert1  mark      #:bus    _        _        _        _        _       ) R)
  ((insert1  _    ) (insert1  #:prev    #:bus    _        _        _        _        _       ) R)
  ((insert1  blank) (insert2  #:prev    _        _        _        _        _        _       ) L)
  ((insert1  space) (insert2  #:prev    _        _        _        _        _        _       ) L)
  ((insert2  _    ) (insert2  _         _        _        _        _        _        _       ) L)
  ((insert2  mark ) (#:return #:arg     _        _        _        _        _        _       ) N)))

(define hanoi
 (make-TM
  'start
  '(halt)
  'blank
  'space
  '_
  rules
  #:registers registers
  #:name 'TM-hanoi))

(define (test n)
 (define ones (make-list n 1))
 (define-values (nr-of-moves state tape) (hanoi (append '(tower A B C) ones)))
 (define (expected n f t r)
  (if (zero? n) '()
   (append
    (expected (sub1 n) f r t)
    (append (list 'move f t r) (make-list n 1))
    (expected (sub1 n) r t f))))
 (define expected-tape (expected n 'A 'B 'C))
 (printf "~s ~s~n" n nr-of-moves)
 (equal? tape expected-tape))

(for/and ((n (in-range 1 9))) (test n))
   
