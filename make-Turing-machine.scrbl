#lang scribble/manual

@(require
  scribble/core
  scribble/eval
  racket/match
  racket
  scribble/html-properties
  "make-Turing-machine.rkt"
  (for-label "make-Turing-machine.rkt"
             racket (only-in typed/racket Setof Exact-Nonnegative-Integer Sequenceof))
  (for-syntax racket))

@; With thanks to Dupéron Georges
@(define (defform-remove-empty-lines the-defform)
   (match the-defform
     [(box-splice
       (list
        before ...
        (nested-flow nf-style
                     (list
                      (table t-style
                             (list other ...
                                   (list
                                    (table (style "specgrammar" tspec-style)
                                           (list lines ...)))
                                   more ...))))
        after ...))
      (define without-empty-lines
        ;; an empty lines is a sequence of five empty columns:
        (remove* (list
                  (list
                   (paragraph (style #f '(omitable)) (element #f (list (element 'tt '(nbsp)))))
                   (paragraph (style #f '(omitable)) (element #f (list (element 'tt '(nbsp)))))
                   (paragraph (style #f '(omitable)) (element #f (list (element 'tt '(nbsp)))))
                   (paragraph (style #f '(omitable)) (element #f (list (element 'tt '(nbsp)))))
                   (paragraph (style #f '(omitable)) (element #f (list (element 'tt '(nbsp)))))))
                 lines))
      (box-splice
       (append
        before
        (list (nested-flow nf-style
                           (list
                            (table t-style
                                   (append other
                                           (list (list
                                                  (table (style "specgrammar" tspec-style)
                                                         without-empty-lines)))
                                           more)))))
        after))]))

@(define-syntax-rule (rack x) (nonbreaking(racket x)))
@(define (inset . x) (apply nested #:style 'inset x))
@(define (note . x) (inset (apply smaller x)))
        
@title[#:version ""]{Turing-machines}
@author{Jacob J. A. Koot}
@(defmodule "make-Turing-machine.rkt" #:packages ())

@section{Introduction}
The reader is supposed to be familiar with Turing-machines.
The combination of the current content of the tape and
the current position of the read/write-head is
represented by two lists: @rack[head] and @rack[tail].
The content of the represented tape is

@inset[@rack[(append (reverse head) tail)]]

The @rack[tail] never is empty.
The first element of the @rack[tail] marks the current position of the read/write-head.
Initially the @rack[head] is empty and the @rack[tail] is the @italic{@element['tt "input"]},
which is a list of @italic{@element['tt "tape-symbol"]}s.
If the @italic{@element['tt "input"]} is empty,
the @rack[tail] initially consists of one @italic{@element['tt "machine-blank"]}.
A move is determined by the current @italic{@element['tt "state"]} of the finite control unit
and the element currently under the read/write-head.
The finite control unit makes moves.
A move consists of three optional steps:@(linebreak)

@inset{
1: putting the control unit in another @italic{@element['tt "state"]},@(linebreak)
2: replacing the element under the read/write-head by another element and@(linebreak)
3: moving the read/write-head one step to the right or to the left.}

We consider the last element of the tail to be at the right end of the content of the tape.

@note{In real life tape equipment usually the tape is moving
while the read/write-head remains in fixed position.
Moving the read/write-head has the same effect as keeping it in fixed position and moving
the tape in opposit direction.
Exchange `left' with `right' if you
prefer to think in terms of moving the tape rather than the read-write/head.
You can also think of an infinitely wide typewriter with moving head but without linefeed.
When writing a letter or space on a spot where a letter is already present,
it must erase the present letter before writing the new letter.
The words `left' and `right' can be confusing.
What is left and right depends on the position from which you are looking.
When looking at the tape equipment or the typewriter from the other side,
left and right are exchanged.
When looking to the north, west is at your left,
but looking to the south puts west at your right.
Looking in a mirror you see your right arm at the right,
but it is the left arm of the image in the mirror.
We consider the first element of a list to be at the left and
the last element to be at the right, no matter from which side we are looking.
Now we have to decide where the first element of a list is and where the last one,
but this is easy. Obviously @rack[(car lst)] must be considered to be the first element
of @rack[lst].}

@note{In some writings the state of a Turing-machine is defined such as to include
both the state of the control unit and the content of the tape.
In this document the @italic{@element['tt "state"]} refers to the control unit only and
does not include the current content of the tape.}

The representation of the tape and the current position of the read/write-head
allows fast implementation of moves,
independent of the size of the content.
The machine refuses to write @italic{@element['tt "machine-blank"]}s and
@italic{@element['tt "dummy-symbol"]}s,
but can write a @italic{@element['tt "user-blank"]},
which is a @italic{@element['tt "tape-symbol"]} too.
@italic{@element['tt "machine-blank"]}s are used only to extend the tape
at the left or at the right of the current content.
When moving the read/write-head at the left of the start or
at the right of end of the current content of the tape,
a @italic{@element['tt "machine-blank"]} is added and
the read/write-head is positioned at this @italic{@element['tt "machine-blank"]}.
In this way an infinite tape is simulated with an infinite number of
@italic{@element['tt "machine-blank"]}s both at the left and at the right of the actual content.
The @italic{@element['tt "dummy-symbol"]} is for use in @italic{@element['tt "rules"]} only.
The machine repeats moves until a @italic{@element['tt "final-state"]} is obtained,
or remains making moves forever if it never reaches a @italic{@element['tt "final-state"]}.
The input must not contain @italic{@element['tt "machine-blank"]}s nor
@italic{@element['tt "dummy-symbol"]}s.
The @italic{@element['tt "state"]}s and @italic{@element['tt "tape-symbol"]}s
can be arbitrary Racket values,
but usually symbols and exact integer numbers are the most convenient ones.
Using lists for @italic{@element['tt "tape-symbol"]}s
allows the simulation of multi-tape Turing-machines.
Equivalence relation @rack[equal?] is used for comparison of two @italic{@element['tt "state"]}s
or two @italic{@element['tt "tape-symbol"]}s.
The @italic{@element['tt "state"]}s and @italic{@element['tt "tape-symbol"]}s
live in separate worlds. A @italic{@element['tt "state"]} never is compared to a
@italic{@element['tt "tape-symbol"]}.
Hence the Turing-machine will not be confused when the intersection of the set of
@italic{@element['tt "state"]}s and the set of @italic{@element['tt "tape-symbol"]}s is not empty
or when a @italic{@element['tt "state"]} equals the @italic{@element['tt "dummy-symbol"]} or
the @italic{@element['tt "machine-blank"]}.
After reaching a @italic{@element['tt "final-state"]} the Turing-machine
returns its output as @rack[(append (reverse head) tail)],
but without heading and trailing @italic{@element['tt "machine-blank"]}s or
@italic{@element['tt "user-blank"]}s.
The output can contain @italic{@element['tt "user-blank"]}s but not at the start or the end.
The ouput never contains a @italic{@element['tt "machine-blank"]} or a
@italic{@element['tt "dummy-symbol"]}.

@section{Procedures}
@defform-remove-empty-lines[@defform[#:kind "procedure"
(make-Turing-machine
 starting-state final-states machine-blank user-blank dummy-symbol rules)
#:grammar(
(starting-state state)
(final-states   (state ...))
(rules          (rule ...))
(rule           ((old-state old-symbol) (new-state new-symbol move)))
(final-state    state)
(old-state      state)
(new-state      state)
(old-symbol     tape-symbol dummy-symbol machine-blank)
(new-symbol     tape-symbol dummy-symbol)
(tape-symbol    non-blank user-blank))
#:contracts ((state         any/c)
             (non-blank     any/c)
             (machine-blank any/c)
             (user-blank    any/c)
             (dummy-symbol  any/c)
             (move (or/c 'R 'L 'N)))]{
Procedure @rack[make-Turing-machine] checks its arguments to satisfy the following conditions,
where equality always is to be understood in the sense of @rack[equal?].

@itemlist[
 @item{The @rack[user-blank], the @rack[machine-blank] and the @rack[dummy-symbol]
       must be distinct.}
 @item{A @rack[new-symbol] must not be equal to the @rack[machine-blank].}
 @item{Each @rack[new-state] must appear as the @rack[old-state] of a @rack[rule]
       or must be one of the @rack[final-state]s.}
 @item{Every @rack[rule] must have a distinct combination @rack[(old-state old-symbol)].}
 @item{A @rack[move] must be @rack['R], @rack['L] or @rack['N].}]

The @rack[rules] are converted to two hashes in order to speed up finding a @rack[rule]
that applies. One of the hashes is for all rules where
the @rack[old-symbol] equals the @rack[dummy-symbol],
the other one for all rules where
the @rack[old-symbol] is not equal to the @rack[dummy-symbol].
The hashes are consulted in a way such that a @rack[rule] whose @rack[old-symbol] is not the
@rack[dummy-symbol] prevails over a rule with the same @rack[old-state] and
whose @rack[old-symbol] is the @rack[dummy-symbol].
Hence, read @rack[(old-state dummy-symbol)] as applying to all remaining @rack[tape-symbol]s
and the @rack[machine-blank]
not appearing as an @rack[old-symbol] in a rule with the same @rack[old-state].@(linebreak) 
@rack[move] @rack['L] indicates that the read-write-head moves to the left
(or the tape to the right).@(linebreak)
@rack[move] @rack['R] indicates that the read-write-head moves to the right
(or the tape to the left).@(linebreak)
@rack[move] @rack['N] indicates that that the read-write-head (or the tape) does not move.

A rule of the form

@inset[@rack[((old-state old-symbol) (new-state new-symbol move))]]

where the @rack[old-symbol] is not the @rack[dummy-symbol]
applies when the @rack[old-state] equals the current @rack[state]
and the element currently under the read/write-head equals the @rack[old-symbol].
A rule of the form

@inset[@rack[((old-state dummy-symbol) (new-state new-symbol move))]]

accepts every arbitrary element currently under the read/write-head.
A rule of the form

@inset[@rack[((old-state old-symbol) (new-state dummy-symbol move))]]

does not alter the element under the the read/write-head.
However, if the element is a @rack[machine-blank],
it is replaced by a @rack[user-blank].

@(elemtag "Turing-machine" "")
Procedure @rack[make-Turing-machine] produces a Turing-machine represented by a procedure:

@defproc[#:kind "procedure" #:link-target? #f
(Turing-machine (input (listof tape-symbol)))
(values final-state (listof tape-symbol))]{
Heading and trailing @rack[user-blank]s and @rack[machine-blank]s
are removed from the output before it is returned.
If during the execution of the @elemref["Turing-machine" "Turing-machine"]
no rule can be found matching the current @rack[state] and the
element below the read/write-head, an exception is raised.}

@defparam*[Turing-report on/off any/c boolean?]{
If @rack[on/off] is not @rack[#f], the new value is @rack[#t].
The initial value is @rack[#f].
When the value of parameter @rack[Turing-report] is true,
a @(elemref "Turing-machine" (element 'tt "Turing-machine")) reports each move
on the current output-port.
Each line of the report shows:

@itemlist[
@item{the old @rack[state]}
@item{the new @rack[state]}
@item{the @rack[tape-symbol] (or @rack[machine-blank]) encountered before replacing it}
@item{the @rack[tape-symbol] that is written}
@item{the move (@rack['R], @rack['L] or @rack['N])}
@item{the new position of the read/write-head and the new content of the tape shown as
the result of @rack[(list (reverse head) tail)],
the first element of @rack[tail] marking the position of the read/write-head.}]

The report is best readable when the printed forms of @rack[state]s
do not vary much in their lengths.
The same holds for @rack[tape-symbol]s.}}]

@defparam*[Turing-limit n any/c boolean?]{
When the parameter holds an @rack[exact-positive-integer?], say n,
a @(elemref "Turing-machine" (element 'tt "Turing-machine"))
halts with an exception when it does not reach a final state within n or less moves.
The initial value is @rack[#f].
When @rack[n] is not an @rack[exact-positive-integer?],
the parameter is set to hold @rack[#f].} Example:

@interaction[
(require racket "make-Turing-machine.rkt")
(define rules
'(((1 _) (2 _ N))
  ((2 _) (3 _ N))
  ((3 _) (4 _ N))
  ((4 _) (F _ N))))
(define TM (make-Turing-machine '1 '(F) 'B 'b '_ rules))
(Turing-report #t)
(Turing-limit 0)
(Turing-limit)
(TM '())
(Turing-limit 4)
(TM '())
(Turing-limit 3)
(TM '())]

@defparam*[Turing-move-width n exact-nonnegative-integer? exact-nonnegative-integer?]{
In a report the move counter is padded with blanks such as to take @rack[n] characters.
Move counts requiring more characters are not truncated.
The initial value is @rack[0].}

@(define (tt x) (nonbreaking (element 'tt x)))

@section{Examples}

Some of the ideas used in the examples are based on material of Jay McCarthy
that can be found in @hyperlink["http://jeapostrophe.github.io/2013-10-29-tmadd-post.html"
                                "http://jeapostrophe.github.io/2013-10-29-tmadd-post.html"].

@subsection{Erase elements}
The following Turing-machine always terminates.
A correct input is @tt["(x ... [+ x ...] ...)"].
The result of a correct input is the input without @tt["+"].
This is like addition of zero, one or more natural numbers,
where natural number n is written as `@tt["x ..."]' with n @tt["x"]s.
With a correct input the machine halts in state @tt["T"].
With incorrect input the machine halts in state @tt["F"].
The machine never moves left of the start of the input.
Capital letter @tt["B"] is the machine-blank,
@tt["b"] the user-blank and @tt["_"] the dummy-symbol.

@interaction[
(require racket "make-Turing-machine.rkt")
(code:comment "")
(define rules
'((code:comment "       State 0 : Inspect the very first element.")
  (code:comment "                 Mark start x with y or start + with p.")
  (code:comment "                 This way we can detect the start of the input")
  (code:comment "                 when moving left and avoid moving left")
  (code:comment "                 of the start of the input.")
  ((0 x) (1 y R))  (code:comment "Ok, go check the remainder of the input.")
  ((0 +) (1 p R))  (code:comment "Ok, go check the remainder of the input.")
  ((0 B) (T b N))  (code:comment "Empty input accepted.")
  ((0 _) (F _ N))  (code:comment "Reject incorrect input.")
  (code:comment "       State 1 : Check the remainder of the input.")
  ((1 x) (1 x R))  (code:comment "Ok, continue the check.")
  ((1 +) (1 + R))  (code:comment "Ok, continue the check.")
  ((1 B) (2 b L))  (code:comment "Input is ok. Start the addition.")
  ((1 _) (F _ N))  (code:comment "Reject incorrect input.")
  (code:comment "       State 2 : Do the addition from right to left.")
  (code:comment "                 The content starts with y or p and ends with b.")
  ((2 x) (2 x L))  (code:comment "Leave x as it is and continue addition.")
  ((2 y) (T x N))  (code:comment "Start of input reached. Done.")
  ((2 +) (3 x R))  (code:comment "Replace + by x and go erase the last x.")
  ((2 p) (3 y R))  (code:comment "Replace p by y and go erase the last x.")
  (code:comment "       State 3 : Go to end of tape.")
  ((3 x) (3 x R))  (code:comment "Keep looking for end of input.")
  ((3 b) (4 b L))  (code:comment "End of input reached. Go erase one x.")
  (code:comment "       State 4 : Erase the last x or the y if there is no x.")
  ((4 x) (2 b L))  (code:comment "Erase x and continue addition.")
  ((4 y) (T b N))  (code:comment "Erase y and accept.")
  ))
(code:comment "")
(Turing-move-width 2)
(code:comment "")
(define Turing-machine (make-Turing-machine '0 '(T F) 'B 'b '_ rules))
(code:comment "")
(Turing-report #t)
(code:comment "")
(Turing-machine '())
(Turing-machine '(x + x))
(Turing-machine '(x x x + x x))
(Turing-machine '(x + x x + x x x))
(Turing-machine '(x x x +))
(Turing-machine '(+ x x))
(Turing-machine '(+))
(Turing-machine '(x x x x x))
(Turing-machine '(x))
(Turing-machine '(+ +))
(Turing-machine '(+ x +))
(Turing-machine '(x x + x + x))
(code:comment "")
(code:comment "The following examples yield state F.")
(code:comment "")
(Turing-machine '(x x b x x))
(Turing-machine '(z))
(Turing-machine '(y x x z x x))
(Turing-machine '(x + x z x))
(code:comment "")
(code:comment "The following example yields an exception.")
(code:comment "")
(Turing-machine '(x x x B x x x))]

@subsection{Binary addition}
The following Turing-machine adds two binary numbers.
The machine always terminates.
A correct input is defined as follows:

@inset{@verbatim[
"input   = (operand + operand)
operand = bit bit ...
bit     = 0
bit     = 1"]}

An incorrect input yields state @element['tt "F"].
A correct input yields state @element['tt "T"] and output
@nonbreaking{(bit bit ...)}
showing the sum of the two operands.
More precisely the output is @nonbreaking{(1 bit ...)} or (0),
id est, without leading zeros.
@element['tt "B"] is the machine-blank,
@element['tt "b"] the user-blank and @element['tt "_"] the dummy-symbol.
The initial content of the tape is modified such as to result in the sum.
A 0 bit is replaced by symbol @element['tt "x"] and a 1 bit by symbol
@element['tt "y"] as soon as it is known.
During the addition the content of the tape is
@nonbreaking{@element['tt "(bit-0-or-1 ... x-or-y ... + bit-0-or-1 ...)"]}.
Bits of the second operand are processed starting from the least significant one.
Every such bit is erased before it is processed.
The significance of the erased bit is the same a that of the right-most bit-0-or-1
of the first operand.
After all bits of the second operand have been processed,
the @element['tt "+"] is erased,
@element['tt "x"] and @element['tt "y"] are reverted to
@element['tt "0"] and @element['tt "1"] and leading zeros are removed.

@interaction[
(require racket "make-Turing-machine.rkt")
(code:comment "")
(define rules
'((code:comment "Check the input.")
  (code:comment "At least one bit required preceding +.")
  ((0 0) (1 0 R)) (code:comment "Ok, continue parsing the first operand.")
  ((0 1) (1 1 R)) (code:comment "Ok, continue parsing the first operand.")
  ((0 _) (F _ N)) (code:comment "Reject.")
  (code:comment "Check the remainder of the first operand.")
  ((1 0) (1 0 R)) (code:comment "Continue checking the first operand.")
  ((1 1) (1 1 R)) (code:comment "Continue checking the first operand.")
  ((1 +) (2 + R)) (code:comment "End of first operand, go to second operand.")
  ((1 _) (F _ N)) (code:comment "Reject.")
  (code:comment "At least one bit required for the second operand.")
  ((2 0) (3 0 R)) (code:comment "Ok, continue parsing the second operand.")
  ((2 1) (3 1 R)) (code:comment "Ok, continue parsing the second operand.")
  ((2 _) (F _ N)) (code:comment "Reject.")
  (code:comment "Check the remainder of the second operand.")
  ((3 0) (3 0 R)) (code:comment "Ok, continue parsing the second operand.")
  ((3 1) (3 1 R)) (code:comment "Ok, continue parsing the second operand.")
  ((3 B) (4 b L)) (code:comment "End of correct input. Go to the addition.")
  ((3 _) (F _ N)) (code:comment "Reject.")
  (code:comment "Addition")
  (code:comment "We are at the least significant bit of the second operand.")
  ((4 0) (5 b L)) (code:comment "Erase the bit and add it to the first operand.")
  ((4 1) (7 b L)) (code:comment "Erase the bit and add it to the first operand.")
  (code:comment "Adding bit 0.")
  (code:comment "Look for the least significant bit of the first operand.")
  ((5 +) (6 + L)) (code:comment "Least significant bit of first operand found.")
  ((5 _) (5 _ L)) (code:comment "Continue looking for first operand.")
  ((6 x) (6 x L)) (code:comment "Skip bits already computed.")
  ((6 y) (6 y L)) (code:comment "Skip bits already computed.")
  ((6 0) (A x R)) (code:comment "Mark bit as having been computed.")
  ((6 1) (A y R)) (code:comment "Mark bit as having been computed.")
  ((6 B) (A x R)) (code:comment "Add a bit marked as having been computed.")
  ((6 b) (A x R)) (code:comment "Add a bit marked as having been computed.")
  (code:comment "Adding bit 1.")
  (code:comment "Look for the least significant bit of the first operand.")
  ((7 +) (8 + L)) (code:comment "Least significant bit of first operand found.")
  ((7 _) (7 _ L)) (code:comment "Continue looking for first operand.")
  ((8 x) (8 x L)) (code:comment "Skip bits already computed.")
  ((8 y) (8 y L)) (code:comment "Skip bits already computed.")
  ((8 0) (A y R)) (code:comment "Put a 1 bit as having been computed.")
  ((8 1) (9 x L)) (code:comment "Put a zero bit as being computed and process carry.")
  ((8 b) (A y R)) (code:comment "Add the bit.")
  ((8 B) (A y R)) (code:comment "Add the bit.")
  (code:comment "Process a carry.")
  ((9 0) (A 1 R))
  ((9 1) (9 0 L))
  ((9 b) (A 1 R))
  ((9 B) (A 1 R))
  (code:comment "Go to next least significant bit of second operand.")
  ((A b) (B b L)) (code:comment "End of second operand.")
  ((A _) (A _ R)) (code:comment "Keep on looking.")
  (code:comment "Here we are at the least significant bit of the second operand.")
  ((B 0) (5 b L)) (code:comment "Remove bit from the second operand and go add it.")
  ((B 1) (7 b L)) (code:comment "Remove bit from the second operand and go add it.")
  ((B +) (C b L)) (code:comment "Second operand totaly processed. Erase the + sign.")
  (code:comment "Addition is complete.")
  (code:comment "Revert x to 0 and y to 1.")
  ((C x) (C 0 L))
  ((C y) (C 1 L))
  ((C 0) (C 0 L))
  ((C 1) (C 1 L))
  ((C b) (D b R))
  ((C B) (D b R))
  (code:comment "Remove heading zeros, but make sure at least one bit remains.")
  ((D 0) (D b R))
  ((D 1) (T 1 N))
  ((D b) (T 0 N))
  ((D B) (T 0 N))))
(code:comment "")
(define adder (make-Turing-machine '0 '(T F) 'B 'b '_ rules))
(code:comment "")
(Turing-move-width 2)
(code:comment "")
(code:comment "Some examples with report.")
(code:comment "")
(parameterize ((Turing-report #t))
 (adder '(0 + 0)))
(parameterize ((Turing-report #t))
 (adder '(0 + 1)))
(parameterize ((Turing-report #t))
 (adder '(1 + 0)))
(parameterize ((Turing-report #t))
 (adder '(1 + 1)))
(code:comment "")
(code:comment "Two examples without report.")
(code:comment "")
(adder '(1 0 1 0 + 1 1 1 1 1))
(adder '(1 1 1 1 1 + 1 0 1 0))
(code:comment "")
(code:comment "Checking the Turing-machine.")
(code:comment "We'll need two procedures for conversion between")
(code:comment "exact nonnegative integer numbers and lists of bits.")
(code:comment "")
(code:comment "Procedure exact-nonnegative-integer->list-of-bits converts")
(code:comment "exact nonnegative integer n to a list of w (or more) bits 0 and 1.")
(code:comment "")
(define (exact-nonnegative-integer->list-of-bits n w)
 (cond
  ((zero? n)
   (make-list w 0))
  ((even? n)
   (append
    (exact-nonnegative-integer->list-of-bits (quotient n 2) (max 0 (sub1 w)))
    (list 0)))
  (else
   (append
    (exact-nonnegative-integer->list-of-bits (quotient n 2) (max 0 (sub1 w)))
    (list 1)))))
(code:comment "")
(code:comment "Procedure list-of-bits->exact-nonnegative-integer converts")
(code:comment "a list of bits 0 and 1 to an exact nonnegative integer")
(code:comment "")
(define (list-of-bits->exact-nonnegative-integer lst)
 (let loop ((r 0) (lst (reverse lst)) (e 1))
  (cond
   ((null? lst) r)
   ((= (car lst) 0) (loop r (cdr lst) (* 2 e)))
   ((= (car lst) 1) (loop (+ r e) (cdr lst) (* 2 e))))))
(code:comment "")
(code:comment "Check that list-of-bits->exact-nonnegative-integer is")
(code:comment "the inverse of exact-nonnegative-integer->list-of-bits.")
(code:comment "")
(for*/and
 ((w (in-range 1 20))
  (n (in-range 0 20)))
 (= n
  (list-of-bits->exact-nonnegative-integer
   (exact-nonnegative-integer->list-of-bits n w))))
(code:comment "")
(code:comment "Test the Turing-machine.")
(code:comment "")
(for*/and ((w (in-range 1 10)) (code:comment "Width for n.")
           (n (in-range 0 20))
           (u (in-range 1 10)) (code:comment "Width for m.")
           (m (in-range 0 20)))
 (define-values (state output)
  (adder
   (append
    (exact-nonnegative-integer->list-of-bits n w)
    (list '+)
    (exact-nonnegative-integer->list-of-bits m u))))
 (and (eq? state 'T)
  (= (list-of-bits->exact-nonnegative-integer output) (+ n m))))]

@subsection{Decimal addition}
The following machine expects @nonbreaking{@element['tt "((n m) ...)"]} as input,
where each @element['tt "n"] and each @element['tt "m"] is an exact integer between 0 (inclusive)
and 10 (exclusive).
The machine adds the numbers @element['tt "n..."] and @element['tt "m..."] and returns the sum
@element['tt "s..."]
However the machine considers the first digit as the least significant one and
the last digit as the most significant one.
The machine does one pass through the input only.
During each step it moves to the right.
It replaces each input symbol @nonbreaking{@element['tt "(n m)"]} by one decimal digit.
State @element['tt "0"] indicates that there is no carry.
State @element['tt "1"] indicates that a carry must be added.
State @element['tt "0"] is the initial state and @element['tt "T"] the final state.

@interaction[
(require racket "make-Turing-machine.rkt")
(code:comment "")
(define rules
 (append
  (for*/list ((n (in-range 0 10)) (m (in-range 0 10)))
   (list (list 0 (list n m))
    (let ((sum (+ n m)))
     (if (> sum 9) (list 1 (- sum 10) 'R)
                   (list 0 sum 'R)))))
  (for*/list ((n (in-range 0 10)) (m (in-range 0 10)))
   (list (list 1 (list n m))
    (let ((sum (+ n m 1)))
     (if (> sum 9) (list 1 (- sum 10) 'R)
                   (list 0 sum 'R)))))
  (list
   '((0 B) (T b R))
   '((1 B) (T 1 N)))))
(code:comment "")
(define TM (make-Turing-machine 0 '(T) 'B 'b '_ rules))
(code:comment "")
(code:comment "nr->lst takes an exact nonnegative integer and")
(code:comment "returns its list of digits from least to most significant one.")
(code:comment "")
(define (nr->lst n)
 (define (nr->lst n)
  (cond
   ((zero? n) '())
   (else
    (define-values (q r) (quotient/remainder n 10))
    (cons r (nr->lst q)))))
 (if (zero? n) '(0) (nr->lst n)))
(code:comment "")
(code:comment "prepare-input takes two exact nonnegative integers")
(code:comment "and returns the corresponding input for TM.")
(code:comment "")
(define (prepare-input n m)
 (let ((n (nr->lst n)) (m (nr->lst m)))
  (define ln (length n))
  (define lm (length m))
  (define len (max ln lm))
  (map list (append n (make-list (- len ln) 0))
            (append m (make-list (- len lm) 0)))))
(code:comment "")
(code:comment "output->nr converts the output of the TM")
(code:comment "to an exact nonnegative integer.")
(code:comment "")
(define (output->nr lst)
 (if (null? lst) 0
  (+ (car lst) (* 10 (output->nr (cdr lst))))))
(code:comment "")
(code:comment "Example with report.")
(code:comment "")
(let ((n 9876) (m 987654))
 (parameterize ((Turing-report #t))
  (let-values (((state output) (TM (prepare-input n m))))
   (define sum (output->nr output))
   (values sum (= sum (+ n m))))))
(code:comment "")
(code:comment "Test the TM.")
(code:comment "")
(for/and ((k (in-range 0 1000)))
 (define n (random 1000000000))
 (define m (random 1000000000))
 (define-values (state output) (TM (prepare-input n m)))
 (and (= (output->nr output) (+ n m)) (eq? state 'T)))]

@subsection{Busy beaver}
3 state busy beaver. In fact there are four states, but final state @tt{T} does not count.

@interaction[
(require racket "make-Turing-machine.rkt")
(define rules
 '(((A 0) (B 1 R))
   ((A 1) (C 1 L))
   ((B 0) (A 1 L))
   ((B 1) (B 1 R))
   ((C 0) (B 1 L))
   ((C 1) (T 1 R))))
(define TM
 (make-Turing-machine
  'A (code:comment "  The initial state.")
  '(T) (code:comment "The final state.")
  0 (code:comment "   The machine-blank.")
  'user-blank-not-used
  'dummy-symbol-not-used
  rules))
(Turing-report #t)
(Turing-move-width 2)
(TM '())]

@larger{@larger{@bold{The end}}}