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
  (define 5blanks
   (make-list 5 (paragraph (style #f '(omitable)) (element #f (list (element 'tt '(nbsp)))))))
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
     (remove* (list 5blanks) lines))
    (box-splice
     (append
      before
      (list
       (nested-flow nf-style
        (list
         (table t-style
          (append other
           (list
            (list (table (style "specgrammar" tspec-style) without-empty-lines))) more)))))
      after))]))

@(define-syntax-rule (rack x) (nonbreaking(racket x)))
@(define (inset . x) (apply nested #:style 'inset x))
@(define (note . x) (inset (apply smaller x)))
@(define (itel x) (italic (element 'tt x)))
@(define (tt x) (nonbreaking (element 'tt x)))

@title[#:version ""]{Turing-machines}
@author{Jacob J. A. Koot}
@(defmodule "make-Turing-machine.rkt" #:packages ())

@section{Introduction}
This document describes procedure @rack[make-Turing-machine].
It is a tool for the construction of procedures that emulate two-way single tape
@hyperlink["https://en.wikipedia.org/wiki/Turing_machine" "Turing-machines"].
John E. Hopcroft and Jeffrey D. Ullman give a very accurate description of
@hyperlink["https://en.wikipedia.org/wiki/Turing_machine" "Turing-machines"]
in their book “Formal Languages and their Relation to Automata” (ISBN 0-201-0298 3-9)
The reader of the present documentation is supposed to be familiar with Turing-machines.
Nevertheless, a survey of the terminology as used in this document.

@(image "Turing-machine.gif")

The @itel["internal-state"] of a Turing-machine is that of the control unit.
The state of a Turing-machine as a whole includes the @itel["internal-state"],
the current content of the tape and the current position of the read/write-head.
The first element of the content is considered to be at the left,
the last element to be at the right.
The current element is the one currently below the read/write-head.
The elements of the content are @itel["tape-symbols"],
but the first or last element can be an @itel["empty-cell"],
which is not a @itel["tape-symbol"].
Initially the content consists of the @itel["input"]
and the read/write-head is positioned at the leftmost element.
If the @itel["input"] is empty, the
content of the tape initially consists of one @itel["empty-cell"].
The control unit makes moves according to its @itel["rules"].
A move is determined by the @itel["internal-state"]
of the control unit and the current element under the read/write-head.
A move consists of three steps:

@itemlist[
@item{Optionally putting the control unit in another @itel["internal-state"].}
@item{Optionally replacing the current element by
another one. This step is not optional when
the current element is an @itel["empty-cell"].
The latter always is replaced by a @itel["tape-symbol"].}
@item{Optionally moving the read/write-head one step to the right or to the left.}]

@note{In real life tape equipment usually the tape is moving
while the read/write-head remains in fixed position.
Moving the read/write-head has the same effect as keeping it in fixed position and moving
the tape in opposit direction.}

The machine never writes a @itel["dummy"] or @itel["empty-cell"].
It cannot remove any element of the content of the tape,
but it can replace the current element by a @itel["blank"],
which is a @itel["tape-symbol"].
@itel["Empty-cells"] are used only to extend the tape
at the left or at the right of the current content.
When moving the read/write-head at the left of the begin of the content of the tape
or at the right of the end, an @itel["empty-cell"] is added and
the read/write-head is positioned at this @itel["empty-cell"].
In this way an infinite tape is simulated with an infinite number of
@itel["empty-cells"] both at the left and at the right of the actual content.
In fact the content never has more than one @itel["empty-cell"].
If it has one, it is the first element or the last one and the read/write-head is positioned at it.
In this situation either the @itel["empty-cell"] is immediately replaced by a
@itel["tape-symbol"] during the next move or,
when the last move has produced a @itel["final-state"],
the machine immediately halts without replacing the @itel["empty-cell"].
The @itel["dummy"] is for use in @itel["rules"] only.
The @itel["rules"] describe how the control unit makes its moves.
The machine repeats moves until a @itel["final-state"] is obtained,
or may remain making moves forever if it never reaches a @itel["final-state"].
It is possible to put a maximum on the number of moves
such as to raise an exception when the emulated machine needs more moves.
See parameter @rack[Turing-limit].
It may happen that there is no @itel["rule"] specifying which move to make
for a given combination of @itel["internal-state"] and current element.
In that case the procedure that emulates the Turing-machine halts by raising an exception.
The @itel["internal-states"] and @itel["tape-symbols"] can be arbitrary Racket values,
but usually symbols and exact integer numbers are the most convenient ones.
Using lists or vectors for @itel["tape-symbols"] and/or @itel["internal-states"]
allows the simulation of multi-tape Turing-machines,
although this may require many @itel["rules"].
Procedure @rack[make-Turing-machine] is designed primarily for single tape Turing-machines.
Equivalence relation @rack[equal?] is used for comparison of two @itel["internal-states"]
or two @itel["tape-symbols"].
The @itel["internal-states"] and @itel["tape-symbols"] live in separate worlds.
An @itel["internal-state"] never is compared to a @itel["tape-symbol"] or an @itel["empty-cell"].
Hence the Turing-machine will not be confused when the intersection of the set of
@itel["internal-states"] and the set of @itel["tape-symbols"] is not empty
or when an @itel["internal-state"] equals the @itel["dummy"] or an @itel["empty-cell"].
However, this may confuse a human reader.
After reaching a @itel["final-state"] the Turing-machine returns its @tt{output},
which consists of the content of the tape,
but without heading or trailing @itel["empty-cell"] or @itel["blanks"].
The @tt{output} can contain @itel["blanks"] but not at the start or the end.
The @tt{output} never contains an @itel["empty-cell"] or a @itel["dummy"].

@note{Procedure @rack[make-Turing-machine] produces a procedure
@(seclink "Turing-machine" (element 'tt "Turing-machine")) in which the internal
representation of the tape and the rules is such that
each move is made in constant time, independent of the number of @itel{rules},
the size of the content of the tape and the position of the read/write-head.
The maximal time needed to prepare the @tt["output"] after reaching
a @itel["final-state"] depends linearly on the size of the content.
The maximal time procedure @rack[make-Turing-machine] needs to produce a
@(seclink "Turing-machine" (element 'tt "Turing-machine")) is
a linear function of the number of @itel{rules}.}

@section{Procedures}
@defform-remove-empty-lines[@defform[#:kind "procedure"
(make-Turing-machine
 initial-state final-states empty-cell blank dummy rules)
#:grammar(
(initial-state internal-state)
(final-states  (final-state ...))
(blank         tape-symbol)
(rules         (rule ...))
(rule          ((old-state old-symbol) (new-state new-symbol move)))
(final-state   internal-state)
(old-state     internal-state)
(new-state     internal-state)
(old-symbol    tape-symbol dummy empty-cell)
(new-symbol    tape-symbol dummy))
#:contracts ((internal-state any/c)
             (   tape-symbol any/c)
             (    empty-cell any/c)
             (         dummy any/c)
             (          move (or/c 'R 'L 'S)))]{
Procedure @rack[make-Turing-machine] returns a procedure that emulates a Turing-machine.
Before the machine is produced the arguments are checked to satisfy the following conditions,
equality or being distinct to be understood in the sense of @rack[equal?].

@itemlist[
 @item{The @rack[blank], the @rack[empty-cell] and the @rack[dummy]
       must be distinct.}
 @item{The @rack[empty-cell] must not be used as a @rack[new-symbol].}
 @item{A @rack[final-state] must not be used as an @rack[old-state].}
 @item{The @rack[rules] must have distinct combinations @rack[(old-state old-symbol)].}
 @item{A @rack[move] must be @rack['R], @rack['L] or @rack['S].}]

When not all of these conditions are satisfied,
procedure @rack[make-Turing-machine] raises an error.
The @rack[rules] are interpreted as follows,
where equality again is to be understood in the sense of @rack[equal?].

@itemlist[
@item{A Turing-machine halts when its current @rack[internal-state] equals a @rack[final-state].}
@item{A @rack[rule] applies if its @rack[old-state] equals the current @rack[internal-state]
of the control unit and the @rack[old-symbol] matches the current element.}
@item{The @rack[dummy] matches every current element.
Every other @rack[old-symbol] matches only when equal to the current element.}
@item{A @rack[rule] whose @rack[old-state] equals the current @rack[internal-state] and
whose @rack[old-symbol] equals the current element
prevails over a @rack[rule] with the same @rack[old-state] and
whose @rack[old-symbol] is the @rack[dummy].}
@item{When a rule is applied, the current @rack[internal-state] is changed to the @rack[new-state].}
@item{If the @rack[new-symbol] is not the @rack[dummy],
the current element is replaced by the @rack[new-symbol].}
@item{If the @rack[new-symbol] is the @rack[dummy] and
the current element is not the @rack[empty-cell],
the current element remains as it is.}
@item{If the @rack[new-symbol] is the @rack[dummy] and
the current element is the @rack[empty-cell],
the current element is replaced by a @rack[blank].}
@item{The read/write-head may be moved depending on the @rack[move]
of the @rack[rule].@(linebreak)
@rack[move] @rack['L] indicates a move to the left.@(linebreak)
@rack[move] @rack['R] indicates a move to the right.@(linebreak)
@rack[move] @rack['S] indicates that that the read-write-head stays where it is.}
@item{When no matching rule can be found,
the procedure emulating the Turing-machine halts by raising an exception.}]

@defproc[(Turing-report) void?]{
Prints a report of the most recently run @(seclink "Turing-machine" (element 'tt "Turing-machine")).
Uses the @rack[current-output-port].
Each line of the report shows:

@itemlist[
@item{The move counter, starting from 1.}
@item{The @rack[old-state] of the control unit.}
@item{The @rack[new-state] of the control unit, possibly the same as the @rack[old-state].}
@item{The @rack[tape-symbol] (or @rack[empty-cell]) encountered before replacing it.}
@item{The @rack[tape-symbol] that is written, possibly the same one as just read.}
@item{The @rack[move] of the read/write-head (@rack['R], @rack['L] or @rack['S]).}
@item{The new position of the read/write-head and the new content of the tape shown as
@element['tt "((h ...) (t ...))"],
where @element['tt "(h ... t ...)"] is the content of the tape and the leftmost
@element['tt "t"] marks the new position of the read/write-head.
@element['tt "(h ...)"] may be empty, but @element['tt "(t ...)"] never is empty,
although it can consist of the @rack[empty-cell] only.}]} Example:

@interaction[
(require "make-Turing-machine.rkt")
(define TM (make-Turing-machine
            'A      (code:comment "initial state")
            '(Halt) (code:comment "final state")
            'E      (code:comment "empty cell")
            'B      (code:comment "blank")
            '_      (code:comment "dummy")
            '(((A _) (AA x S))
              ((AA _) (AAA xx S))
              ((AAA _) (Halt xxx S)))))
(TM '())
(Turing-report)]
                                                 
@defparam*[Turing-limit n (or/c #f exact-positive-integer?) (or/c #f exact-positive-integer?)
           #:value #f]{
When the parameter holds an @rack[exact-positive-integer?], say n,
a @(seclink "Turing-machine" (element 'tt "Turing-machine"))
halts with an exception when it does not reach a @rack[final-state] within n or less moves.
See the next section for examples.}

@section[#:tag "Turing-machine"]{Running a Turing-machine}
A procedure returned by procedure @rack[make-Turing-machine],
say @element['tt @larger{@bold{Turing-machine}}], is called as follows:

@defproc[#:kind "procedure" #:link-target? #f
(Turing-machine (input (listof tape-symbol)))
(values nr-of-moves final-state output)]{
@rack[nr-of-moves] : @rack[exact-positive-integer?]@(linebreak)
@rack[output] : @rack[(listof tape-symbol)]

The @rack[output] shows the content of the tape after the machine has reached a
@rack[final-state], but without
heading or trailing @rack[blank]s or @rack[empty-cell].
If during the execution of the @(seclink "Turing-machine" (element 'tt "Turing-machine"))
no rule can be found matching its current @rack[internal-state] and the current element,
the @(seclink "Turing-machine" (element 'tt "Turing-machine")) halts by raising an exception.

Many @(seclink "Turing-machine" (element 'tt "Turing-machines")) never halt,
sometimes depending on the @rack[rules] only,
sometimes depending on both the @rack[rules] and the @rack[input].
In some cases the problem can be predicted by looking at the @rack[rules]
or can be detected while a @(seclink "Turing-machine" (element 'tt "Turing-machine")) is running.
However, because of the
@hyperlink["https://en.wikipedia.org/wiki/Halting_problem"]{@bold{Halting Problem}}
it is not possible to avoid the problem in all cases.
Procedure @rack[make-Turing-machine] and the
@(seclink "Turing-machine" (element 'tt "Turing-machines"))
it produces do no checks at all against non-halting.
For example, the following trivial @(seclink "Turing-machine" (element 'tt "Turing-machine"))
clearly will loop forever with arbitrary input:

@interaction[
(require racket "make-Turing-machine.rkt")
(define TM (make-Turing-machine
            'A   (code:comment "initial state")
            '(T) (code:comment "final states")
            'E   (code:comment "empty cell")
            'B   (code:comment "blank")
            '_   (code:comment "dummy")
            '(((A _) (A _ S)))))
(code:line (Turing-limit 5) (code:comment "Prevent the machine to run forever."))
(TM '())
(Turing-report)]

In this example @rack[rule] @rack['((A _) (A _ S))] alone already implies an infinite loop.
While the @rack[TM] is running,
its state (the content of the tape and the position of the read/write-head included)
never changes after the first move,
which could be detected while the @rack[TM] is running.
As another example consider:

@interaction[
(require racket "make-Turing-machine.rkt")
(define TM (make-Turing-machine
            'A   (code:comment "initial state")
            '(T) (code:comment "final states")
            'E   (code:comment "empty cell")
            'B   (code:comment "blank")
            '_   (code:comment "dummy")
            '(((A _) (A _ R)))))
(Turing-limit 5)
(TM '())
(Turing-report)]

By means of mathematical induction it is easily proven that the above machine never halts,
although it never reproduces the same state.

@note{Procedure @rack[make-Turing-machine] could be adapted such as to
predict the infinite loops of the last two examples just by checking the rules.
It also could be adapted such as to produce a
@(seclink "Turing-machine" (element 'tt "Turing-machine"))
that can detect a repeated state. These adaptations have not been made,
for the Halting Problem implies that there always remain cases
in which a non-halting case cannot be predicted
by procedure @rack[make-Turing-machine] and cannot be detected while a
@(seclink "Turing-machine" (element 'tt "Turing-machine")) with given @rack[input] is running.
Moreover, detection of a repeated state requires a record of all visited states,
which may involve a lot of memory.}}}]

@section{Examples}

Some of the ideas used in the examples are based on material of Jay McCarthy
that can be found in @hyperlink["http://jeapostrophe.github.io/2013-10-29-tmadd-post.html"
                                "http://jeapostrophe.github.io/2013-10-29-tmadd-post.html"].

@subsection{Erase elements}
The following Turing-machine always halts.
A correct input is @tt["(x ... [+ x ...] ...)"],
where the square brackets indicate an optional part of the input.
The result of a correct input is the input without @tt["+"].
This is like addition of zero, one or more natural numbers,
where natural number n is written as `@tt["x ..."]' with n @tt["x"]s.
With a correct input the machine halts with @rack[final-state] @tt["T"].
With incorrect input the machine halts with @rack[final-state] @tt["F"].
The machine never moves left of the start of the input.

@interaction[
(require racket "make-Turing-machine.rkt")
(code:comment " ")
(define rules
'((code:comment "       State 0 : Inspect the very first element.")
  (code:comment "                 Mark start x with y or start + with p.")
  (code:comment "                 This way we can detect the start of the input")
  (code:comment "                 when moving left and avoid moving left")
  (code:comment "                 of the start of the input.")
  ((0 x) (1 y R))  (code:comment "Ok, go check the remainder of the input.")
  ((0 +) (1 p R))  (code:comment "Ok, go check the remainder of the input.")
  ((0 E) (T B S))  (code:comment "Empty input accepted.")
  ((0 _) (F _ S))  (code:comment "Reject incorrect input.")
  (code:comment "       State 1 : Check the remainder of the input.")
  ((1 x) (1 x R))  (code:comment "Ok, continue the check.")
  ((1 +) (1 + R))  (code:comment "Ok, continue the check.")
  ((1 E) (2 B L))  (code:comment "Input is ok. Start the addition.")
  ((1 _) (F _ S))  (code:comment "Reject incorrect input.")
  (code:comment "       State 2 : Do the addition from right to left.")
  (code:comment "                 When entering state 2 for the first time the read/")
  (code:comment "                 write-head is at the right-most non-blank element.")
  (code:comment "                 The content starts with y or p and ends with B.")
  ((2 x) (2 x L))  (code:comment "Leave x as it is and continue addition.")
  ((2 y) (T x S))  (code:comment "Start of input reached. Done.")
  ((2 +) (3 x R))  (code:comment "Replace + by x and go replacing the last x by a blank.")
  ((2 p) (3 y R))  (code:comment "Replace p by y and go replacing the last x by a blank.")
  (code:comment "       State 3 : Go to end of tape.")
  ((3 x) (3 x R))  (code:comment "Keep looking for end of input.")
  ((3 B) (4 B L))  (code:comment "End of input reached.")
  (code:comment "       State 4 : Replace the last x (or the y if there is no x) by a blank.")
  ((4 x) (2 B L))  (code:comment "Replace x by a blank and continue addition.")
  ((4 y) (T B S))  (code:comment "Replace y by a blank and accept.")))
(code:comment " ")
(define TM (make-Turing-machine
            '0     (code:comment "initial state")
            '(T F) (code:comment "final states")
            'E     (code:comment "empty cell")
            'B     (code:comment "blank")
            '_     (code:comment "dummy")
            rules))
(code:comment " ")
(TM '(x + x x + x x x))
(Turing-report)
(code:comment " ")
(code:comment "The following examples yield final state F.")
(code:comment " ")
(TM '(z))
(TM '(y x x z x x))
(TM '(x + x z x))
(TM '(x x x B x x x))
(code:comment " ")
(code:comment "The following two examples yield exceptions,")
(code:comment "even before the TM starts running.")
(code:comment " ")
(TM '(x x x E x x x))
(TM '(x x x _ x x x))
(code:comment " ")
(code:comment "More tests:")
(code:comment " ")
(random-seed 0)
(code:comment " ")
(for/and ((nx (in-range 0 50)))
 (define expected (make-list nx 'x))
 (for/and ((n+ (in-range 10)))
  (define input (append (make-list n+ '+) expected))
  (for/and ((n (in-range 10)))
   (define-values (nr-of-moves final-state output) (TM (shuffle input)))
   (and (eq? final-state 'T) (equal? output expected)))))]

@subsection{Binary addition}
The following Turing-machine adds two natural numbers written in binary notation.
The machine halts with every arbitrary input.
A correct input is defined as follows:

@inset{@verbatim[
"input   = (operand + operand)
operand = bit bit ...
bit     = 0 | 1"]}

An incorrect input yields final state @element['tt "F"].
A correct input yields final state @element['tt "T"] and @tt{output}
@nonbreaking{@rack[(bit bit ...)]}
showing the sum of the two operands.
More precisely the @tt{output} is @nonbreaking{@rack[(1 bit ...)]} or @rack[(0)],
id est, without leading zeros.
The initial content of the tape is modified such as to result in the sum.
In the sum a 0 bit is written as @element['tt "x"] and a 1 bit as @element['tt "y"].
During the addition the content of the tape is (ignoring blanks and empty-cell) 
@nonbreaking{@element['tt "(0-or-1 ... x-or-y ... + 0-or-1 ...)"]}.
Bits of the second operand are processed starting from the least significant one.
Every such bit is replaced by a @itel["blank"] before it is processed.
The significance of the blanked bit is the same as that of
the right-most @nonbreaking{@element['tt "bit-0-or-1"]} of the first operand.
After all bits of the second operand have been processed,
the @element['tt "+"] is removed,
elements @element['tt "x"] and @element['tt "y"] are reverted to
@element['tt "0"] and @element['tt "1"] and leading zeros are removed.

@interaction[
(require racket "make-Turing-machine.rkt")
(code:comment " ")
(define rules
'((code:comment "Check the input.")
  (code:comment "At least one bit required preceding +.")
  ((0 0) (1 0 R)) (code:comment "Ok, continue parsing the first operand.")
  ((0 1) (1 1 R)) (code:comment "Ok, continue parsing the first operand.")
  ((0 _) (F _ S)) (code:comment "Reject.")
  (code:comment "Check the remainder of the first operand.")
  ((1 0) (1 0 R)) (code:comment "Continue checking the first operand.")
  ((1 1) (1 1 R)) (code:comment "Continue checking the first operand.")
  ((1 +) (2 + R)) (code:comment "End of first operand, go to second operand.")
  ((1 _) (F _ S)) (code:comment "Reject.")
  (code:comment "At least one bit required for the second operand.")
  ((2 0) (3 0 R)) (code:comment "Ok, continue parsing the second operand.")
  ((2 1) (3 1 R)) (code:comment "Ok, continue parsing the second operand.")
  ((2 _) (F _ S)) (code:comment "Reject.")
  (code:comment "Check the remainder of the second operand.")
  ((3 0) (3 0 R)) (code:comment "Ok, continue parsing the second operand.")
  ((3 1) (3 1 R)) (code:comment "Ok, continue parsing the second operand.")
  ((3 E) (4 B L)) (code:comment "End of correct input. Go to the addition.")
  ((3 _) (F _ S)) (code:comment "Reject.")
  (code:comment "Addition")
  (code:comment "We are at the least significant bit of the second operand.")
  ((4 0) (5 B L)) (code:comment "Erase the bit and add it to the first operand.")
  ((4 1) (7 B L)) (code:comment "Erase the bit and add it to the first operand.")
  (code:comment "Adding bit 0.")
  (code:comment "Look for the least significant bit of the first operand.")
  ((5 +) (6 + L)) (code:comment "Least significant bit of first operand found.")
  ((5 _) (5 _ L)) (code:comment "Continue looking for first operand.")
  ((6 x) (6 x L)) (code:comment "Skip bits already computed.")
  ((6 y) (6 y L)) (code:comment "Skip bits already computed.")
  ((6 0) (A x R)) (code:comment "Mark bit as having been computed.")
  ((6 1) (A y R)) (code:comment "Mark bit as having been computed.")
  ((6 E) (A x R)) (code:comment "Add a bit marked as having been computed.")
  ((6 B) (A x R)) (code:comment "Add a bit marked as having been computed.")
  (code:comment "Adding bit 1.")
  (code:comment "Look for the least significant bit of the first operand.")
  ((7 +) (8 + L)) (code:comment "Least significant bit of first operand found.")
  ((7 _) (7 _ L)) (code:comment "Continue looking for first operand.")
  ((8 x) (8 x L)) (code:comment "Skip bits already computed.")
  ((8 y) (8 y L)) (code:comment "Skip bits already computed.")
  ((8 0) (A y R)) (code:comment "Put a 1 bit as having been computed.")
  ((8 1) (9 x L)) (code:comment "Put a zero bit as being computed and process carry.")
  ((8 B) (A y R)) (code:comment "Add the bit.")
  ((8 E) (A y R)) (code:comment "Add the bit.")
  (code:comment "Process a carry.")
  ((9 0) (A 1 R))
  ((9 1) (9 0 L))
  ((9 B) (A 1 R))
  ((9 E) (A 1 R))
  (code:comment "Go to next least significant bit of second operand.")
  ((A B) (B B L)) (code:comment "End of second operand.")
  ((A _) (A _ R)) (code:comment "Keep on looking.")
  (code:comment "Here we are at the least significant bit of the second operand.")
  ((B 0) (5 B L)) (code:comment "Remove bit from the second operand and go add it.")
  ((B 1) (7 B L)) (code:comment "Remove bit from the second operand and go add it.")
  ((B +) (C B L)) (code:comment "Second operand totaly processed. Erase the + sign.")
  (code:comment "Addition is complete.")
  (code:comment "Revert x to 0 and y to 1.")
  ((C x) (C 0 L))
  ((C y) (C 1 L))
  ((C 0) (C 0 L))
  ((C 1) (C 1 L))
  ((C B) (D B R))
  ((C E) (D B R))
  (code:comment "Remove heading zeros, but make sure at least one bit remains.")
  ((D 0) (D B R))
  ((D 1) (T 1 S))
  ((D B) (T 0 S))
  ((D E) (T 0 S))))
(code:comment " ")
(define adder (make-Turing-machine
               '0     (code:comment "initial state")
               '(T F) (code:comment "final states")
               'E     (code:comment "empty cell")
               'B     (code:comment "blank")
               '_     (code:comment "dummy")
               rules))
(code:comment " ")
(adder '(1 0 1 1 + 1 0 1 1 1))
(Turing-report)
(code:comment " ")
(adder '(0 0 0 1 1 + 0 0 1 1))
(Turing-report)
(code:comment " ")
(adder '(0 0 0 + 0 0))
(Turing-report)
(code:comment " ")
(code:comment "Checking the Turing-machine.")
(code:comment "We need two procedures for conversion between")
(code:comment "exact nonnegative integer numbers and lists of bits.")
(code:comment " ")
(code:comment "Procedure exact-nonnegative-integer->list-of-bits converts")
(code:comment "exact nonnegative integer n to a list of bits 0 and 1.")
(code:comment " ")
(define (exact-nonnegative-integer->list-of-bits n)
 (reverse
  (let loop ((n n))
   (cond
    ((zero? n) '(0))
    ((even? n) (cons 0 (loop (quotient n 2))))
    (else      (cons 1 (loop (quotient n 2))))))))
(code:comment " ")
(code:comment "Procedure list-of-bits->exact-nonnegative-integer converts")
(code:comment "a list of bits 0 and 1 to an exact nonnegative integer")
(code:comment " ")
(define (list-of-bits->exact-nonnegative-integer lst)
 (let loop ((r 0) (lst (reverse lst)) (e 1))
  (cond
   ((null? lst) r)
   ((= (car lst) 0) (loop r (cdr lst) (* 2 e)))
   ((= (car lst) 1) (loop (+ r e) (cdr lst) (* 2 e))))))
(code:comment " ")
(code:comment "Check that list-of-bits->exact-nonnegative-integer is")
(code:comment "the inverse of exact-nonnegative-integer->list-of-bits.")
(code:comment " ")
(random-seed 0)
(for*/and ((m (in-range 0 100)))
 (define n (if (< m 50) m (random 30000000)))
 (= n
  (list-of-bits->exact-nonnegative-integer
   (exact-nonnegative-integer->list-of-bits n))))
(code:comment " ")
(code:comment "Test the Turing-machine.")
(code:comment " ")
(for*/and ((n (in-range 0 100))
           (m (in-range 0 100)))
 (define input
  (append
   (exact-nonnegative-integer->list-of-bits n)
   (list '+)
   (exact-nonnegative-integer->list-of-bits m)))
 (define-values (nr-of-moves final-state output) (adder input))
 (and (eq? final-state 'T)
  (= (list-of-bits->exact-nonnegative-integer output) (+ n m))))]

@subsection{Decimal addition}
The following machine expects @nonbreaking{@element['tt "((n m) ...)"]} as input,
where each @element['tt "n"] and each @element['tt "m"] is a decimal digit coded as
an exact integer between 0 (inclusive) and 10 (exclusive).
The machine adds the numbers @element['tt "n..."] and @element['tt "m..."] and returns the sum
@element['tt "s..."]
However the machine considers the first digit as the least significant one and
the last digit as the most significant one.
The machine passes exactly once through the input.
During each step it moves to the right.
Redundant heading zeros are not removed.
It replaces each input symbol @nonbreaking{@element['tt "(n m)"]} by one decimal digit.
State @element['tt "0"] indicates that there is no carry.
State @element['tt "1"] indicates that a carry must be added.
State @element['tt "0"] is the initial internal-state and @element['tt "T"] the final state.

@interaction[
(require racket "make-Turing-machine.rkt")
(code:comment " ")
(define rules
 (append
  (list
   '((0 E) (T B R))
   '((1 E) (T 1 R)))
  (for*/list
   ((c (in-range 0 2))  (code:comment "0 = no carry, 1 = carry")
    (n (in-range 0 10)) (code:comment "digit of first operand")
    (m (in-range 0 10)) (code:comment "digit of second operand"))
   (define-values (q r) (quotient/remainder (+ n m c) 10))
   `((,c (,n ,m)) (,q ,r R)))))
(code:comment " ")
(pretty-print rules)
(code:comment " ")
(define TM (make-Turing-machine
            0    (code:comment "initial state")
            '(T) (code:comment "final state")
            'E   (code:comment "empty cell")
            'B   (code:comment "blank")
            '_   (code:comment "dummy")
            rules))
(code:comment " ")
(call-with-values
 (λ () (TM (reverse (map list '(0 0 9) '(0 0 9)))))
 (λ (nr-of-moves final-state content) (reverse content)))
(code:comment " ")
(code:comment "nr->lst takes an exact nonnegative integer and")
(code:comment "returns its list of digits from least to most significant one.")
(code:comment " ")
(define (nr->lst n)
 (define (nr->lst n)
  (cond
   ((zero? n) '())
   (else
    (define-values (q r) (quotient/remainder n 10))
    (cons r (nr->lst q)))))
 (if (zero? n) '(0) (nr->lst n)))
(code:comment " ")
(code:comment "prepare-input takes two exact nonnegative integers")
(code:comment "and returns the corresponding input for TM.")
(code:comment " ")
(define (prepare-input n m)
 (let ((n (nr->lst n)) (m (nr->lst m)))
  (define ln (length n))
  (define lm (length m))
  (define len (max ln lm))
  (map list (append n (make-list (- len ln) 0))
            (append m (make-list (- len lm) 0)))))
(code:comment " ")
(code:comment "output->nr converts the output of the TM")
(code:comment "to an exact nonnegative integer.")
(code:comment " ")
(define (output->nr lst)
 (if (null? lst) 0
  (+ (car lst) (* 10 (output->nr (cdr lst))))))
(code:comment " ")
(code:comment "Example with report.")
(code:comment " ")
(let ((n 9876) (m 987654))
 (let-values (((nr-of-moves final-state output) (TM (prepare-input n m))))
  (Turing-report)
  (define sum (output->nr output))
  (values sum (= sum (+ n m)))))
(code:comment " ")
(code:comment "Test the TM.")
(code:comment " ")
(for/and ((k (in-range 0 1000)))
 (define n (random 1000000000))
 (define m (random 1000000000))
 (define-values (nr-of-moves final-state output) (TM (prepare-input n m)))
 (and (= (output->nr output) (+ n m)) (eq? final-state 'T)))]

@subsection{Busy beaver}
3 state busy beaver. In fact there are four states, but final state @tt{T} does not count.

@interaction[
(require racket "make-Turing-machine.rkt")
(define rules
 '(((A 0) (C 1 R))
   ((A 1) (A 1 R))
   ((B 0) (A 1 R))
   ((B 1) (C 1 L))
   ((C 0) (B 1 L))
   ((C 1) (T 1 S))))
(define TM
 (make-Turing-machine
  'A   (code:comment "The initial state.")
  '(T) (code:comment "The final state.")
  0    (code:comment "The empty-cell.")
  'blank-not-used
  'dummy-not-used
  rules))
(TM '())
(Turing-report)]

4 state busy beaver. In fact there are five states, but final state @tt{T} does not count.

@interaction[
(require racket "make-Turing-machine.rkt")
(define rules
 '(((A 0) (B 1 R)) ((A e) (B 1 R))
   ((B 0) (A 1 L)) ((B e) (A 1 L))
   ((C 0) (T 1 R)) ((C e) (T 1 R))
   ((D 0) (D 1 R)) ((D e) (D 1 R))
   ((A 1) (B 1 L))
   ((B 1) (C 0 L))
   ((C 1) (D 1 L))
   ((D 1) (A 0 R))))
(define TM
 (make-Turing-machine
  'A   (code:comment "The initial state.")
  '(T) (code:comment "The final state.")
  'e   (code:comment "The empty-cell.")
  'blank-not-used
  'dummy-not-used
  rules))
(TM '())
(Turing-report)]

@subsection{Zeros and ones}

The following Turing-machine halts on every arbitrary input.
If the input is a list of zeros and ones with as many zeros as ones,
the final state is @rack['T].
In all other cases the final state is @rack['F].
The machine accepts an empty input immediately.
If the input is not empty, a starting mark @rack['s] is added at the left,
the input is checked to consist of zeros and ones only
and an ending mark @rack['e] is added at the end of the input.
Now the read/write-head is at the element immediately left of the end mark @rack['e].
The following process is repeated until halted.
Starting from the right, the machine looks at the left for a @rack[0] or a @rack[1].
If a @rack[0] is encountered, it is replaced by @rack['e] and a required @rack[1] is looked for.
If a @rack[1] is encountered, it is replaced by @rack['e] and a required @rack[0] is looked for.
After finding a required @rack[0] or @rack[1], it is replaced by a blank,
the read/write-head is positioned at the right of the tape
and the process is repeated until no more ones or zeros are present.
If a required @rack[0] or @rack[1] is not found, the machine halts with state @rack['F].

@interaction[
(require racket "make-Turing-machine.rkt")
(code:comment " ")
(define rules
 '((code:comment "state 0: starting state.")
   (code:comment "Accept empty input, otherwise add starting mark s.")
   ((0 E) (T B S)) (code:comment "Accept empty input.")
   ((0 _) (1 _ L))
   ((1 E) (2 s R))
   (code:comment "state 2: Check that we have 0s and 1s only and add an ending mark e.")
   ((2 0) (2 0 R))
   ((2 1) (2 1 R))
   ((2 E) (3 e S))
   ((2 _) (F _ S))
   (code:comment "state 3: Go to the end of the tape.")
   ((3 e) (4 e L))
   ((3 _) (3 _ R))
   (code:comment "state 4: look for a 0 or a 1 at the left")
   ((4 s) (T B S)) (code:comment "Ok, no more 0s or 1s.")
   ((4 0) (5 e L)) (code:comment "a 1 at the left is required.")
   ((4 1) (6 e L)) (code:comment "a 0 at the left is required.")
   ((4 B) (4 e L))
   (code:comment "state 5: look for a required 1 at the left.")
   ((5 0) (5 0 L)) (code:comment "skip 0.")
   ((5 1) (3 B R)) (code:comment "found.")
   ((5 s) (F s S)) (code:comment "no 1 found.")
   ((5 B) (5 B L))
   (code:comment "state 6: look for a required 0 at the left.")
   ((6 0) (3 B R)) (code:comment "found.")
   ((6 1) (6 1 L)) (code:comment "skip 1.")
   ((6 s) (F s S)) (code:comment "no 0 found.")
   ((6 B) (6 B L))))
(code:comment " ")
(define TM
 (make-Turing-machine
  0      (code:comment"initial state")
  '(T F) (code:comment"final states")
  'E     (code:comment"empty cell")
  'B     (code:comment"blank")
  '_     (code:comment"dummy")
  rules))
(code:comment " ")
(TM '(0 1 0 0 1 1 1 0))
(Turing-report)
(code:comment " ")
(code:comment "Let's do some tests.")
(code:comment " ")
(define (test input expected)
 (define-values (n s t) (TM input))
 (or (eq? expected s)
  (error 'test "this is wrong: ~s ~s ~s ~s" input n s t)))
(code:comment " ")
(for*/and ((n0 (in-range 0 10)) (n1 (in-range 0 10)))
 (define input (append (make-list n0 0) (make-list n1 1)))
 (for/and ((n (in-range 0 100)))
  (test (shuffle input) (if (= n0 n1) 'T 'F))))]

@subsection{Checking parentheses}

The following machine reads @rack[L] as a left parenthesis
an @rack[R] as a right parenthesis.
The machine halts in state @rack[T] if the parentheses are well balanced
and no other elements occur in the @itel{input}.
In all other cases the machine halts in state @rack[F].
When counting a @rack[L] as @element['tt "+1"] and a @rack[R] as @element['tt "-1"],
going from left to right the addition may never go below zero and must end in zero.
The method is as follows.
First check that the input consists of @rack[L]s and @rack[R]s only.
Put @itel{tape-symbol} @rack[s] at the left of the input
and @itel{tape-symbol} @rack[e] at the right.
This helps detecting the start and the end of the current content of the tape.
Starting from the right go left looking for a @rack[R] whose first preceding non-blank is @rack[L].
When found replace the @rack[L] and the @rack[R] by blanks, go to the right of the input and repeat.
When looking for a @rack[R] all elements appear to be blanks, the machine halts in state @rack[T].
When encountering a @rack[L] before encountering a @rack[R] the parentheses are not balanced
and the machine halts in state @rack[F].

@interaction[
(require "make-Turing-machine.rkt")
(code:comment " ")
(define rules
  (code:comment "state 0")
  (code:comment "accept empty input.")
  (code:comment "put start marker s before non-empty input.")
'(((0 E) (T B S))
  ((0 _) (1 _ L))
  ((1 E) (2 s R))
  (code:comment "state 2")
  (code:comment "check input.")
  (code:comment "put end marker e at end of input.")
  ((2 L) (2 L R))
  ((2 R) (2 R R))
  ((2 E) (3 e L))
  ((2 _) (F _ S))
  (code:comment "state 3")
  (code:comment "we are at the end of the tape.")
  (code:comment "look left for R immediately preceded by L.")
  ((3 B) (3 B L))
  ((3 s) (7 B R)) (code:comment "all done, go blank the end mark e.")
  ((3 R) (4 R L)) (code:comment "found a R.")
  ((3 _) (F _ S))
  ((4 B) (4 B L))
  ((4 L) (5 B R)) (code:comment "found immediately preceeding L, blank the L.")
  ((4 R) (4 R L)) (code:comment "found another R.")
  ((4 _) (F _ S))
  (code:comment "state 5")
  (code:comment "blank the R corresponding to the L just blanked.")
  ((5 R) (6 B R)) 
  ((5 B) (5 B R))
  (code:comment "state 6")
  (code:comment "go to end of tape and repeat.")
  ((6 e) (3 e L))
  ((6 _) (6 _ R))
  (code:comment "state 7")
  (code:comment "blank the e mark and halt in state T.")
  ((7 e) (T B S))
  ((7 _) (7 _ R))))
(code:comment " ")
(define TM (make-Turing-machine 0 '(T F) 'E 'B '_ rules))
(code:comment " ")
(code:comment "The following examples yield final state T")
(code:comment " ")
(TM '()) (Turing-report)
(TM '(L R)) (Turing-report)
(TM '(L R L R L R)) (Turing-report)
(TM '(L L L R R R)) (Turing-report)
(TM '(L L R L R R)) (Turing-report)
(code:comment " ")
(code:comment "The following examples yield final state F")
(code:comment " ")
(TM '(a)) (Turing-report)
(TM '(L a R)) (Turing-report)
(TM '(R)) (Turing-report)
(TM '(L)) (Turing-report)
(TM '(R L)) (Turing-report)
(TM '(R L R L R L R)) (Turing-report)
(TM '(L R L R L R L)) (Turing-report)]

@subsection{Inserting elements}

The following Turing-machine always halts.
For an input consisting of @rack['a]'s and @rack['b]'s only
the final state is @rack['T] and symbol @rack['x] is inserted
between each @rack['a] and an immediately following @rack['b].
The insertion of @rack['x] requires that the elements
preceding the @rack['b] are shifted one cell to the left.
An input containing anything other than @rack['a] or @rack['b]
yields final state @rack['F].
`@rack[0]' is the initial state. `@rack[B]' is the blank.
`@rack[E]' is the empty cell. `@rack[_]' is the dummy symbol.

@interaction[
(require racket "make-Turing-machine.rkt")
(code:comment " ")
(define rules
'(
  (code:comment "Look for a.")
  ((0  a) (1  a R))
  ((0  b) (0  b R))
  ((0  E) (T  B S))
  ((0  _) (F  _ S))
  (code:comment "Next symbol b?")
  ((1  a) (1  a R)) (code:comment "no, look for next a.")
  ((1  b) (2  M L)) (code:comment "yes, mark it M and proceed.")
  ((1  _) (F  _ S))
  ((1  E) (T  B S))
  (code:comment "Rewind the tape.")
  ((2  E) (3  B R))
  ((2  _) (2  _ L))
  (code:comment "Shift every symbol one cell to the left up to mark M.")
  (code:comment "Replace a or b or x by B.")
  (code:comment "Replace preceding B by a or b or x.")
  (code:comment "Replace M by b and replace preceding B by x.")
  ((3  a) (4a B L))
  ((3  b) (4b B L))
  ((3  x) (4x B L))
  ((3  M) (4M b L))
  ((4a B) (5  a R)) (code:comment "Continue the shift.")
  ((4b B) (5  b R)) (code:comment "Continue the shift.")
  ((4x B) (5  x R)) (code:comment "Continue the shift.")
  ((4M B) (0  x R)) (code:comment "Shift completed. Look for next a followed by b.")
  (code:comment "Step to the right of the B and continue the shift.")
  ((5  B) (3  B R))))
(code:comment " ")
(define TM (make-Turing-machine  0 '(T F) 'E 'B  '_ rules))
(code:comment " ")
(code:comment "Example:")
(code:comment " ")
(TM '(b a b a b a)) (Turing-report)
(code:comment " ")
(code:comment "Let's test the TM.")
(code:comment "The following procedure does the same as the TM")
(code:comment "It is used to check the results of the TM.")
(code:comment " ")
(define (ab->axb input)
 (cond
  ((null? input) '())
  ((null? (cdr input)) input)
  ((equal? (take input 2) '(a b))
   (append '(a x b) (ab->axb (cddr input))))
  (else (cons (car input) (ab->axb (cdr input))))))
(code:comment " ")
(random-seed 0)
(code:comment " ")
(for*/and ((na (in-range 10)) (nb (in-range 10)))
 (define ab (append (make-list na 'a) (make-list nb 'b)))
 (for/and ((k (in-range 100)))
  (define input1 (shuffle ab))
  (define input2 (shuffle (cons 'x ab)))
  (define input3 (shuffle (cons 'M ab)))
  (define-values (nr-of-moves1 state1 output1) (TM input1))
  (define-values (nr-of-moves2 state2 output2) (TM input2))
  (define-values (nr-of-moves3 state3 output3) (TM input3))
  (define expect (ab->axb input1))
  (and
   (equal? (ab->axb input1) output1)
   (equal? state1 'T)
   (equal? state2 'F)
   (equal? state3 'F))))]

@larger{@larger{@bold{The end}}}
