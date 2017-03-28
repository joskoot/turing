#lang scribble/manual

@(require
  scribble/core
  scribble/eval
  racket
  scribble/html-properties
  "make-Turing-machine.rkt"
  (for-label "make-Turing-machine.rkt"
             racket (only-in typed/racket Setof Exact-Nonnegative-Integer Sequenceof))
  (for-syntax racket))

@(define-syntax-rule (rack x) (nonbreaking(racket x)))
@(define (inset . x) (apply nested #:style 'inset x))
         
@title[#:version ""]{Turing machines}
@author{Jacob J. A. Koot}
@(defmodule "make-Turing-machine.rkt" #:packages ())

The reader is supposed to be familiar with Turing machines.
The combination of the content of the tape and the current position of the read/write-head is
represented by two lists: @rack[head] and @rack[tail].
The content of the represented tape is

@inset[@rack[(append (reverse head) tail)]]

The @rack[tail] never is empty.
The first element of the @rack[tail] marks the current position of the read/write-head of the tape.
Initially the @rack[head] is empty and the @rack[tail] contains the input.
If the input is empty,
the @rack[tail] initially consists of one @italic{@element['tt "machine-blank"]}.
A move is determined by the current @italic{@element['tt "state"]} and
the element currently under the read/write-head.
A move consists of assuming a new @italic{@element['tt "state"]},
replacing the element under the read/write-head and
moving the read/write-head one step to the right or to the left or leaving it where it is.
(We assume the start of the input at the left,
the tape to keep in place and the read/write-head being moved.
A move to the right/left of the read/write-head is the same as
moving the tape left/right with fixed read/write-head.
Assuming the start of the input to be at the right causes the same exchange of right and left) 
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
The @italic{@element['tt "dummy-symbol"]} is used in rules only.
The machine repeats moves until a @italic{@element['tt "final-state"]} is obtained.
The input must not contain @italic{@element['tt "machine-blank"]}s nor
@italic{@element['tt "dummy-symbol"]}s.
The @italic{@element['tt "state"]}s and @italic{@element['tt "tape-symbol"]}s
can be arbitrary Racket values,
but usually symbols and exact integer numbers are the most convenient ones.
Equivalence relation @rack[equal?] is used for comparison of two @italic{@element['tt "state"]}s
or two @italic{@element['tt "tape-symbol"]}s.
The Turing machine will not be confused when the intersection of the set of
@italic{@element['tt "state"]}s and the set of @italic{@element['tt "tape-symbol"]}s is not empty
or when a @italic{@element['tt "state"]} equals the @italic{@element['tt "dummy-symbol"]} or
the @italic{@element['tt "machine-blank"]}.
After reaching a @italic{@element['tt "final-state"]} the Turing machine
returns its output as @rack[(append (reverse head) tail)],
but without heading and trailing @italic{@element['tt "machine-blank"]}s or
@italic{@element['tt "user-blank"]}s.
The output can contain @italic{@element['tt "user-blank"]}s but not at the start or the end.
The ouput never contains a @italic{@element['tt "machine-blank"]} or a
@italic{@element['tt "dummy-symbol"]}.

@defform[#:kind "procedure"
(make-Turing-machine
 starting-state
 final-states
 machine-blank
 user-blank
 dummy-symbol
 rules)
#:grammar(
(starting-state  state)
(final-states    (state ...))
(rules           (rule ...))
(rule            ((old-state old-symbol) (new-state new-symbol move)))
(final-state     state)
(old-state       state)
(new-state       state)
(old-symbol      tape-symbol machine-blank dummy-symbol)
(new-symbol      tape-symbol dummy-symbol)
(user-blank      tape-symbol))
#:contracts ((state any/c)
             (tape-symbol any/c)
             (machine-blank any/c)
             (dummy-symbol any/c)
             (move (or/c 'R 'L 'N)))]{
The @rack[user-blank], the @rack[machine-blank] and the @rack[dummy-symbol] must be distinct
(in the sense of @rack[equal?]).
A @rack[new-symbol] must not be a @rack[machine-blank].
Each @rack[new-state] must be declared as the @rack[old-state] of a @rack[rule]
or one of the @rack[final-state]s.
@rack[move] @rack['L] indicates a move to the left.
@rack[move] @rack['R] indicates a move to the right.
@rack[move] @rack['N] indicates that no move is to be made.
The machine chooses the first rule that applies.
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
Procedure @rack[make-Turing-machine] produces a Turing machine represented by a procedure:

@defproc[#:kind "procedure" #:link-target? #f
(Turing-machine (input (listof tape-symbol)))
(values final-state (listof tape-symbol))]{
The @rack[input] must not contain @rack[machine-blank]s or @rack[dummy-symbol]s.
The returned list of @rack[tape-symbol]s has no heading or trailing blanks.
If no rule can be found for the current state and the
element below the read/write-head, an exception is raised.}

@defparam*[Turing-report on/off any/c boolean?]{
When @rack[(Turing-report)] is not @rack[#f],
a @(elemref "Turing-machine" (element 'tt "Turing-machine")) reports each move.
Each line of the report shows:

@itemlist[
@item{the old @rack[state]}
@item{the new @rack[state]}
@item{the @rack[tape-symbol] (or @rack[machine-blank]) encountered before replacing it}
@item{the @rack[tape-symbol] that is written}
@item{the move (@rack['R], @rack['L] or @rack['N])}
@item{the new position of the tape-head and the new content shown as
    @rack[(list (reverse head) tail)]}]

If @rack[on/off] is not @rack[#f] the parameter is set to @rack[#t].}}

