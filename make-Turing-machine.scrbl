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

@(define (underline . es)
  (define ul-attrs '((style . "text-decoration: underline")))
  (apply elem es #:style (style #f (list (attributes ul-attrs)))))

@(define-syntax-rule (rack x) (nonbreaking(racket x)))

@(define (make-color-style color elem)
  (define prop:color (color-property color))
  (define color-style (style #f (list prop:color)))
  (element color-style elem))

@(define (red elem) (make-color-style "red" elem))
@(define (green elem) (make-color-style "green" elem))

@(define example-ns (make-base-namespace))

@(parameterize ((current-namespace example-ns))
  (namespace-require 'racket)
  (namespace-require '"make-Turing-machine.rkt"))

@(define-syntax-rule (eval-example expr)
  (nonbreaking (element 'tt (begin (random-seed 0) (format "~s" (eval 'expr example-ns))))))

@(define-syntax (example stx)
  (syntax-case stx ()
   ((_ a)
  #'(begin
     (rack a)
     (hspace 1)
     "→"
     (hspace 1)
     (eval-example a)
     (linebreak)))))

@(define-syntax (example/n stx)
  (syntax-case stx ()
   ((_ a)
  #'(begin
     (rack a)
     (hspace 1)
     "→"
     (linebreak)
     (eval-example a)))))

@(define-syntax-rule (example-table x ...)
  (tabular (list (list @rack[x] "→" (eval-example x)) ...) #:sep (hspace 1)))

@(define(minus) (element 'tt "-"))
@(define(-?) (element "roman" ?-))
@(define (note . x) (inset (apply smaller x)))
@(define (inset . x) (apply nested #:style 'inset x))
@(define-syntax-rule (linespacebreak) @↑{@(hspace 1)@(linebreak)})
@(define (expt-1) @↑{@(minus)1})
@(define ↑ superscript)
@(define ↓ subscript)
@(define (ignore . x) "")
@;(define ignore note)
         
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
the tail initially consists of one @rack[machine-blank].
A move is determined by the current state and the @rack[tape-symbol] under the read/write-head.
A move consists of assuming a new @rack[state], replacing the
@rack[tape-symbol] under the read/write-head and
moving the read/write-head one step to the right or to the left.
The representation of the tape allows fast implementation of moves, independent of the size of
the content. The machine refuses to write @rack[machine-blanks], but can write @rack[user-blanks].
@rack[machine-blank]s are used only to extend the tape at the left or at the right
of the current content.
When moving the read/write-head before the start or beyond the end of the current content
of the tape, a @rack[machine-blank] is added and the read/write-head is positioned at this
@rack[machine-blank].
In this way an infinite tape is simulated with an infinite number of @rack[machine-blank]s both
at the left and at the right of the actual content.
The machine repeats moves until a @rack[final-state] is obtained.
The input must not contain @rack[machine-blank]s.
@rack[state]s and @rack[tape-symbol]s can be arbitrary Racket values,
but usually symbols and exact integer numbers are the most convenient ones.
Equivalence relation @rack[equal?] is used for comparison of two @rack[state]s
or two @rack[tape-symbol]s.
The Turing machine will not be confused when the intersection of the set of @rack[state]s and
the set of @rack[tape-symbol]s is not empty.
After reaching a @rack[final-state] the Turing machine
returns its output as @rack[(append (reverse head) tail)],
but without heading and trailing @rack[machine-blank]s or @rack[user-blank]s.
The output can contain @rack[user-blank]s but not at the start or the end.
The ouput never contains a @rack[machine-blank].

@defform[#:kind "procedure"
(make-Turing-machine
 starting-state
 final-states
 report?
 machine-blank
 user-blank
 rules)
#:grammar(
(starting-state  state)
(final-state     state)
(final-states    (state ...))
(machine-blank   tape-symbol)
(user-blank      tape-symbol)
(rules           (rule ...))
(rule            ((state tape-symbol) (new-state new-symbol move)))
(final-state     state)
(new-state       state)
(new-symbol      tape-symbol)
)
#:contracts ((move (or/c 'R 'L))
             (report? any/c)
             (state any/c)
             (tape-symbol any/c))]{
The @rack[user-blank] and the @rack[machine-blank] must not be the same
(in the sense of @rack[equal?]).
A @rack[new-symbol] must not be a @rack[machine-blank].
Each @rack[new-state] must be the @rack[state] of a @rack[rule] or one of the @rack[final-state]s.
@rack[move] @rack['L] indicates a move to the left.
@rack[move] @rack['R] indicates a move to the right.

@(elemtag "Turing-machine" "")
Procedure @rack[make-Turing-machine] produces a Turing machine represented by a procedure:

@defproc[#:kind "procedure" #:link-target? #f
(Turing-machine (input (listof tape-symbol))) (values final-state (listof tape-symbol))]{
The @rack[input] must not contain @rack[machine-blank]s.
The returned list of @rack[tape-symbol]s has no heading or trailing blanks.
When @rack[report?] is not @rack[#f], the @elemref["Turing-machine" "Turing-machine"]
reports each move. Each line of the report shows:

@itemlist[
@item{the old @rack[state]}
@item{the new @rack[state]}
@item{the @rack[tape-symbol] encountered before replacing it}
@item{the @rack[tape-symbol] that is written}
@item{the move (@rack[R] or @rack[L])}
@item{the new content of the tape shown as @rack[(list (reverse head) tail)]}]

If no rule can be found for the current @rack[state] and the
@rack[tape-symbol] below the read/write-head, an exception is raised.}}