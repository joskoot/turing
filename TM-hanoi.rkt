#lang racket
(require "make-TM.rkt")

#|
The following Turing-machine solves the puzzle of the
@hyperlink["https://en.wikipedia.org/wiki/Tower_of_Hanoi" "Tower of Hanoi"].
It produces the shortest path of moving a tower from one of three pegs to another one.
It expects as input

   tower ‹from› ‹onto› ‹third› 1 ...+

where the number of ones is the height of the tower, id est, the number of disks.
‹from› is the starting peg, ‹onto› the peg of destination and ‹third› the third peg.
The three pegs must be distinct, of course.
Tape-symbols 1, 'tower, 'disk, 'mark and 'markR cannot be used for the names of the pegs.
In the example below the pegs are called 'A, 'B and 'C. 
The machine replaces the input by a sequence of moves

   [disk ‹from› ‹onto› ‹third› 1 ...+] ...+

where the number of ones indicates which disk is moved.
The smallest disk is indicated by one 1.
Each larger disk by one more 1.
The largest disk is marked by as many ones as the height of the tower being moved.
When a tower-instruction is found, it is replaced by a disk-instruction
and when there are two or more disks,
a tower-instruction with one disk less is inserted both at the left and at the right
using the same method of inserting one tape-symbol at a time as in section @secref["Subroutine"].
The machine keeps looking for tower-instructions and halts when there are no more of them.
The following registers are used:

              Required registers.
   #:state  : The primary state.
   #:bus    : The input/output-register.

              Additional registers.
   #:from   : Starting peg.
   #:onto   : Destination peg.
   #:third  : Third peg.

              Registers for subroutines insert} and insertR.
   #:prev   : Previous tape-symbol during insertion.
   #:arg    : Tape-symbol to be inserted.
   #:return : Primary state to be assumed after insertion.|#

(define registers '(#:state #:bus #:prev #:return #:arg  #:from #:onto #:thrd))

(define rules
'(; First look for a tower instruction.
  ; Immediately make it a disk instruction.
  ; If there are no more tower-instructions,
  ; halt in succesful state 'halt.
  
  ((start   tower) (from    disk  _      _        _      _      _      _    ) R)
  ((start   blank) (halt    _     _      _        _      _      _      _    ) N)
  ((start   space) (halt    _     _      _        _      _      _      _    ) N)
  ((start   _    ) (start   _     _      _        _      _      _      _    ) R)

  ; Extract the three pegs of the tower instruction.
  ; Put them in registers #:from, #:onto and #:thrd.

  ((from    _    ) (onto    _     _      _        _      #:bus  _      _    ) R)
  ((onto    _    ) (thrd    _     _      _        _      _      #:bus  _    ) R)
  ((thrd    _    ) (right1  _     _      _        _      _      _      #:bus) R)

  ; Insert a tower instruction at the right.
  ; Copy the height, but with one 1 less.
  ; m1 is a marked 1, the one being copied.
  ; Dont copy the first 1.
  
  ((right1  1    ) (right2  _     _      _        _      _      _      _    ) R)
  ((right2  1    ) (right3  m1    _      _        _      _      _      _    ) R)
  ; If there is one disk only in the original tower-instruction,
  ; do not insert tower-instructions at the left nor at the right.
  ((right2  _    ) (rewind  _     _      _        _      _      _      _    ) L)
  ; Insert a tower instruction at the right.
  ; First go to the right of the new disk-instruction.
  ((right3  1    ) (_       _     _      _        _      _      _      _    ) R)
  ; Insert 'tower and three pegs.
  ((right3  _    ) (insertR _     _      right4   tower  _      _      _    ) N)
  ((right4  _    ) (insertR _     _      right5   #:thrd _      _      _    ) N)
  ((right5  _    ) (insertR _     _      right6   #:onto _      _      _    ) N)
  ((right6  _    ) (insertR _     _      right7   #:from _      _      _    ) N)
  ; Insert a 1.
  ((right7  _    ) (insert  _     _      right8   1      _      _      _    ) N)
  ; Go back to marked 1.
  ((right8  m1   ) (right9  1     _      _        _      _      _      _    ) R)
  ((right8  _    ) (_       _     _      _        _      _      _      _    ) L)
  ; Marked 1 found.
  ; When no more 1s to be copied,
  ; go insert tower-instruction at the left.
  ((right9  tower) (left    _     _      _        _      _      _      _    ) R)
  ; Next 1 to be copied. mark it.
  ((right9   1   ) (right10 m1    _      _        _      _      _      _    ) R)
  ((right10  1   ) (right10 _     _      _        _      _      _      _    ) R)
  ; Go to the tower-instruction being inserted.
  ; skip to the right of the three pegs.
  ((right10 tower) (right11  _     _      _       _      _      _      _    ) R)
  ((right11 _    ) (right12  _     _      _       _      _      _      _    ) R)
  ((right12 _    ) (right13  _     _      _       _      _      _      _    ) R)
  ((right13 _    ) (right14  _     _      _       _      _      _      _    ) R)
  ; We are at the right of the three pegs.
  ; Insert a 1 and go back to the marked 1.
  ((right14 _    ) (insert   _     _      right15 1      _      _      _    ) N)
  ((right15 m1   ) (right16  1     _      _       _      _      _      _    ) R)
  ((right15 _    ) (right15  _     _      _       _      _      _      _    ) L)
  ; Copy next 1.
  ((right16 1    ) (right10  m1    _      _       _      _      _      _    ) R)
  ; No more 1s to be copied,
  ; go inserting tower instruction at the left.
  ((right16 _    ) (left     _     _      _       _      _      _      _    ) L)

  ; Insert a tower instruction at the left.
  ; Copy the height, but with one 1 less.
  ; m1 is a marked 1, the one being copied.

  ((left    _    ) (_        _     _      _       _      _      _      _    ) L)
  ((left    disk ) (left1    _     _      _       _      _      _      _    ) N)
  ((left1   _    ) (insert   _     _      left2   #:onto _      _      _    ) N)
  ((left2   _    ) (insert   _     _      left3   #:thrd _      _      _    ) N)
  ((left3   _    ) (insert   _     _      left4   #:from _      _      _    ) N)
  ((left4   _    ) (insert   _     _      left5   tower  _      _      _    ) N)
  ((left5   _    ) (left5    _     _      _       _      _      _      _    ) R)
  ; Don't copy the first 1.
  ((left5   1    ) (left6    _     _      _       _      _      _      _    ) R)
  ((left6   1    ) (left7    m1    _      _       _      _      _      _    ) L)
  ; No more 1s to be copied.
  ((left6   _    ) (rewind   _     _      _       _      _      _      _    ) L)
  ; Go left to the point where to insert the 1.
  ((left7   _    ) (left7    _     _      _       _      _      _      _    ) L)
  ((left7   disk ) (left8    _     _      _       _      _      _      _    ) N)
  ; Insert the 1.
  ((left8   disk ) (insert   _     _      left9   1      _      _      _    ) N)
  ; Go back to the marked 1.
  ((left9   m1   ) (left10   1     _      _       _      _      _      _    ) R)
  ((left9   _    ) (_        _     _      _       _      _      _      _    ) R)
  ; Copy more 1s, if any left, else rewind and restart.
  ((left10  1    ) (left11   m1    _      _       _      _      _      _    ) L)
  ((left10  _    ) (rewind   _     _      _       _      _      _      _    ) L)
  ((left11  disk ) (insert   _     _      left9   1      _      _      _    ) N)
  ((left11  _    ) (_        _     _      _       _      _      _      _    ) L)

  ; Rewind the tape and
  ; start looking for another tower instruction.

  ((rewind  blank) (start    _     _      _       _      _      _      _    ) R)
  ((rewind  space) (start    _     _      _       _      _      _      _    ) R)
  ((rewind  _    ) (rewind   _     _      _       _      _      _      _    ) L)

  ; Subroutine for insertion of tape-symbol in register #:arg
  ; at the right of the current tape-symbol.
  ; Return in state #:return with
  ; the tape-head at the inserted tape-symbol.
  ; Tape-symbol 'mark or 'markR is used to identify the cell
  ; where to return to and to insert the tape-symbol.
  ; Obviously tape-symbols 'mark and 'markR
  ; must not be used in any other way.
  ; insertR does the same as insert, but ends with the
  ; tape-head at the cell at the right of the inserted cell.

  ((insert  _    ) (insert1  mark   #:bus _       _      _      _      _    ) R)
  ((insert1 _    ) (insert1  #:prev #:bus _       _      _      _      _    ) R)
  ((insert1 blank) (insert2  #:prev _     _       _      _      _      _    ) L)
  ((insert1 space) (insert2  #:prev _     _       _      _      _      _    ) L)
  ((insert2 _    ) (insert2  _      _     _       _      _      _      _    ) L)
  ((insert2 mark ) (#:return #:arg  _     _       _      _      _      _    ) N)
  ((insert2 markR) (#:return #:arg  _     _       _      _      _      _    ) R)
  ((insertR _    ) (insert1  markR  #:bus _       _      _      _      _    ) R)))

(define TM-hanoi
 (make-TM
  'start
  '(halt)
  'blank
  'space
  '_
  rules
  #:registers registers
  #:name 'TM-hanoi))

; 3 disks with report

(TM-hanoi '(tower A B C 1 1 1) #:report 'short)

; Result for 5 disks:

(define-values (nr-of-moves state tape) (TM-hanoi '(tower A B C 1 1 1 1 1)))
(let loop ((tape tape) (move-nr 1))
 (cond
  ((null? tape) (newline))
  ((eq? (car tape) 'disk)
   (printf "~n~a : disk " (~s #:min-width 2 #:align 'right move-nr))
   (loop (cdr tape) (add1 move-nr)))
  (else
   (printf "~s " (car tape))
   (loop (cdr tape) move-nr))))

; Let's test TM-hanoi.

(define (test height)
 (printf " ~n")
 (define ones (make-list height 1))
 (define-values (nr-of-TM-moves state tape)
  (time (TM-hanoi (append '(tower A B C) ones))))
 ; Simple procedure computing the expected results.
 (define (compute-expected height f t r)
  (if (zero? height) '()
   (append
    (compute-expected (sub1 height) f r t)
    (append (list 'disk f t r) (make-list height 1))
    (compute-expected (sub1 height) r t f))))
 ; Compare tape returned by TM-hanoi with expected tape.
 (define expected-tape (compute-expected height 'A 'B 'C))
 (unless (equal? tape expected-tape)
  (error 'TM-hanoi "Wrong results for ~s disks." height))
 ; Show some results.
 (define (disk? x) (eq? x 'disk))
 (define nr-of-hanoi-moves (count disk? tape))
 (define (pad n) (~s #:width 6 #:align 'right n))
 (printf "nr of disks: ~a~nnr of moves: ~a~nnr TM moves: ~a~n"
  (pad height) (pad nr-of-hanoi-moves) (pad nr-of-TM-moves)))

; Test heights 1 up to and including 8 disks.

(for ((height (in-range 1 9))) (test height))
(printf " ~nAll is well.~n")

#|For a tower of h disks the number of times a disk is to be moved is (sub1 (expt 2 h)).
The number of moves of the Turing-machine grows even much faster.
Many moves are required for insertion of tower-instructions.
Subroutine @ttt{insert} handles one tape-symbol at a time only.
Hence the machine frequently must move along possibly large parts of the tape,
first forward to the end of the current tape-content and subsequently
back to the cell being inserted.|#
