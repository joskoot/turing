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
        
@title[#:version ""]{Turing machines}
@author{Jacob J. A. Koot}
@(defmodule "make-Turing-machine.rkt" #:packages ())

@section{Introduction}
The reader is supposed to be familiar with Turing machines.
The combination of the current content of the tape and
the current position of the read/write-head is
represented by two lists: @rack[head] and @rack[tail].
The content of the represented tape is

@inset[@rack[(append (reverse head) tail)]]

The @rack[tail] never is empty.
The first element of the @rack[tail] marks the current position of the read/write-head.
Initially the @rack[head] is empty and the @rack[tail] contains the @italic{@element['tt "input"]},
which is a list of @italic{@element['tt "tape-symbol"]}s.
If the @italic{@element['tt "input"]} is empty,
the @rack[tail] initially consists of one @italic{@element['tt "machine-blank"]}.
A move is determined by the current @italic{@element['tt "state"]} and
the element currently under the read/write-head.
A move consists of assuming a new @italic{@element['tt "state"]},
replacing the element under the read/write-head and
moving the read/write-head one step to the right or to the left or leaving it where it is.
We consider the last element of the tail to be at the right end of the content of the tape.

@note{In real life tape equipment it is usually the tape that moves,
the read/write-head remaining in fixed position.
Moving the read/write-head has the same effect as keeping it in fixed position and moving
the tape in opposit direction.
Hence interchange `moving to the left' with `moving to the right' if you
prefer to think in terms of moving the tape while the read-write/head remains at fixed position.
In fact, the words `left' and `right' can be confusing.
For example, looking to the north, west is at your left,
but looking to the south puts west at your right.
We consider the first element of a list to be at the left and the last element to be at the right.}

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
The machine repeats moves until a @italic{@element['tt "final-state"]} is obtained.
The input must not contain @italic{@element['tt "machine-blank"]}s nor
@italic{@element['tt "dummy-symbol"]}s.
The @italic{@element['tt "state"]}s and @italic{@element['tt "tape-symbol"]}s
can be arbitrary Racket values,
but usually symbols and exact integer numbers are the most convenient ones.
Equivalence relation @rack[equal?] is used for comparison of two @italic{@element['tt "state"]}s
or two @italic{@element['tt "tape-symbol"]}s.
@italic{@element['tt "state"]}s and @italic{@element['tt "tape-symbol"]}s
live in separate worlds. They never are compared to each other.
Hence the Turing machine will not be confused when the intersection of the set of
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

@section{Procedures}
@; With thanks to Dupéron Georges
@defform-remove-empty-lines[@defform[#:kind "procedure"
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
Heading and trailing blanks are removed from the output before it is returned.
If during the execution of the @elemref["Turing-machine" "Turing-machine"]
no rule can be found for the current state and the
element below the read/write-head, an exception is raised.}

@defparam*[Turing-report on/off any/c boolean?]{
If @rack[on/off] is not @rack[#f], the new value is @rack[#t].
When the value of parameter @rack[Turing-report] is true,
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

The report is best readable when the printed form of every @rack[state]
consists of the same number of characters, preferably one character only.
The same holds for @rack[tape-symbol]s.}}]

@(define (tt x) (element 'tt x))

@section{Example}
The following Turing machine terminates for every list of symbols @tt["x"] and @tt["+"].
A correct input is @tt["(x ... [+ x ...] ...)"].
The result of a correct input is the input without @tt["+"].
This is like addition of zero, one or more natural numbers.
With a correct input the machine halts in state @tt["T"].
With incorrect input the machine halts in state @tt["F"]. The states are:

state 0 : Check that the input is correct.@(linebreak)
state 1 : Rewind the tape.@(linebreak)
state 2 : Find leftmost x.@(linebreak)
state 3 : Do the addition@(linebreak)
state 4 : Rewind the tape.@(linebreak)
state 5 : Remove left-most x and continue the addition.

@tt["B"] is the machine-blank, @tt["b"] the user-blank and @tt["_"] the dummy-symbol.

@interaction[
(require racket "make-Turing-machine.rkt")
(define rules
'(((0 x) (0 x R))   (code:comment "Ok, continue checking the input.")
  ((0 +) (0 + R))   (code:comment "Ok, continue checking the input.")
  ((0 B) (1 b L))   (code:comment "End of the input. It is correct. Go rewind the tape.")
  ((0 _) (F _ N))   (code:comment "The input contains an unacceptable symbol.")
  ((1 x) (1 x L))   (code:comment "Keep on rewinding.")
  ((1 +) (1 + L))   (code:comment "Keep on rewinding.")
  ((1 B) (2 b R))   (code:comment "Start of tape reached. Find the first x.")
  ((2 x) (3 x R))   (code:comment "Start the addition.")
  ((2 +) (2 b R))   (code:comment "Ignore heading +.")
  ((2 b) (T b N))   (code:comment "No x or + present.")
  ((2 B) (T b N))   (code:comment "No x or + present.")
  ((3 x) (3 x R))   (code:comment "Accept x.")
  ((3 +) (4 x L))   (code:comment "Replace + by x and go remove the first x.")
  ((3 B) (T b N))   (code:comment "Done.")
  ((3 b) (T b N))   (code:comment "Done.")
  ((4 x) (4 x L))   (code:comment "Go to start of tape.")
  ((4 b) (5 b R))   (code:comment "Start encountered. Go remove first x.")
  ((4 B) (5 b R))   (code:comment "Start encountered. Go remove first x.")
  ((5 x) (3 b R))   (code:comment "Remove first x and continue addition.")
  ))

(define Turing-machine (make-Turing-machine '0 '(T F) 'B 'b '_ rules))

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
(code:comment "The following examples yield state F.")
(Turing-machine '(x x b x x))
(Turing-machine '(z))
(Turing-machine '(y x x z x x))
(Turing-machine '(y + x z x))
(code:comment "Example of report.")
(Turing-report #t)
(Turing-machine '(x x + x x))
]