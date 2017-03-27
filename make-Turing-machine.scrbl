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
Initially the @rack[head] is empty and the @rack[tail] contains the input. If the input is empty,
the tail initially consists of one @italic{@element['tt "machine-blank"]}.
A @italic{@element['tt "move"]} is determined by the current state and the
@italic{@element['tt "tape-symbol"]} under the read/write-head.
A @italic{@element['tt "move"]} consists of assuming a new @italic{@element['tt "state"]},
replacing the @italic{@element['tt "tape-symbol"]} under the read/write-head and
moving the read/write-head one step to the right or to the left or leaving it where it is.
The representation of the tape allows fast implementation of @italic{@element['tt "move"]}s,
independent of the size of the content.
The machine refuses to write @italic{@element['tt "machine-blank"]}s and
@italic{@element['tt "dummy-symbol"]}s,
but can write @italic{@element['tt "user-blank"]}s.
@italic{@element['tt "machine-blank"]}s are used only to extend the tape at the left or at the right
of the current content.
@italic{@element['tt "dummy-symbol"]}s are used in rules.
When moving the read/write-head before the start or beyond the end of the current content
of the tape, a @italic{@element['tt "machine-blank"]} is added and the read/write-head is
positioned at this @italic{@element['tt "machine-blank"]}.
In this way an infinite tape is simulated with an infinite number of
@italic{@element['tt "machine-blank"]}s both at the left and at the right of the actual content.
The machine repeats @italic{@element['tt "move"]}s until a @italic{@element['tt "final-state"]}
is obtained.
The input must not contain @italic{@element['tt "machine-blank"]}s nor
@italic{@element['tt "dummy-symbol"]}s.
@italic{@element['tt "state"]}s and @italic{@element['tt "tape-symbol"]}s
can be arbitrary Racket values,
but usually symbols and exact integer numbers are the most convenient ones.
Equivalence relation @rack[equal?] is used for comparison of two @italic{@element['tt "state"]}s
or two @italic{@element['tt "tape-symbol"]}s.
The Turing machine will not be confused when the intersection of the set of
@italic{@element['tt "state"]}s and the set of @italic{@element['tt "tape-symbol"]}s is not empty.
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
(machine-blank   tape-symbol)
(user-blank      tape-symbol)
(dummy-symbol    tape-symbol)
(rules           (rule ...))
(rule            ((state tape-symbol) (new-state new-symbol move)))
(final-state     state)
(new-state       state)
(new-symbol      tape-symbol))
#:contracts ((move (or/c 'R 'L 'N))
             (state any/c)
             (tape-symbol any/c))]{
The @rack[user-blank], the @rack[machine-blank] and the @rack[dummy-symbol] must be distinct
(in the sense of @rack[equal?]).
A @rack[new-symbol] must not be a @rack[machine-blank].
Each @rack[new-state] must be the @rack[state] of a @rack[rule] or one of the @rack[final-state]s.
@rack[move] @rack['L] indicates a move to the left.
@rack[move] @rack['R] indicates a move to the right.
@rack[move] @rack['N] indicates that no move is to be made.
The machine chooses the first rule that applies.
A rule of the form
@inset[@rack[((state dummy-symbol) (new-state new-symbol move))]]
accepts every arbitrary @italic{@element['tt "tape-symbol"]}.
A rule of the form
 @inset[@rack[((state dummy-symbol) (new-state dummy-symbol move))] " or"@(linebreak)
        @rack[((state tape-symbol) (new-state dummy-symbol move))]]
does not alter the @italic{@element['tt "tape-symbol"]} under the the read/write-head.
However, if the @italic{@element['tt "tape-symbol"]} is the @rack[machine-blank],
it is replaced by a @rack[user-blank].

@(elemtag "Turing-machine" "")
Procedure @rack[make-Turing-machine] produces a Turing machine represented by a procedure:

@defproc[#:kind "procedure" #:link-target? #f
(Turing-machine (input (listof tape-symbol))) (values final-state (listof tape-symbol))]{
The @rack[input] must not contain @rack[machine-blank]s or @rack[dummy-symbol]s.
The returned list of @rack[tape-symbol]s has no heading or trailing blanks.
If no rule can be found for the current @rack[state] and the
@rack[tape-symbol] below the read/write-head, an exception is raised.}

@defparam*[Turing-report on/off any/c boolean?]{
When @rack[(Turing-report)] is not @rack[#f],
a @(elemref "Turing-machine" (element 'tt "Turing-machine")) reports each move.
Each line of the report shows:

@itemlist[
@item{the old @rack[state]}
@item{the new @rack[state]}
@item{the @rack[tape-symbol] encountered before replacing it}
@item{the @rack[tape-symbol] that is written}
@item{the move (@rack['R] or @rack['L])}
@item{the new position of the tape-head and the new content shown as
    @rack[(list (reverse head) tail)]}]

If @rack[on/off] is not @rack[#f] the parameter is set to @rack[#t].}}

