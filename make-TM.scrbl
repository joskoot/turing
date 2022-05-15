#lang scribble/manual

@(require
  racket
  scribble/core
  scribble/eval
  scribble/racket
  "make-TM.rkt"
  (for-template "make-TM.rkt" racket)
  (for-label "make-TM.rkt" racket)
  (for-syntax racket))

@(define-syntax-rule
  (Interaction x ...)
  (interaction
   #:eval
   (make-base-eval
    #:lang
    '(begin
      (require racket "make-TM.rkt")
      (print-reader-abbreviations #f)
      (print-as-expression #f))) x ...))

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

@(define-syntax-rule (rack x ...) (nonbreaking(racket x ...)))
@(define (inset . x) (apply nested #:style 'inset x))
@(define (note . x) (inset (apply smaller x)))
@(define (itel x) (italic (element 'tt x)))
@(define (ttt . x) (nonbreaking (apply element 'tt x)))
@(define (ignore . x) "")

@title[#:version ""]{Turing-machines}
@author{Jacob J. A. Koot}
@(defmodule "make-TM.rkt" #:packages ())

@section{Introduction}

Module @hyperlink["../../make-TM.rkt" "make-TM.rkt"]
provides one binding only, that of procedure @rack[make-TM],
which returns procedures that emulate
@hyperlink["https://en.wikipedia.org/wiki/Turing_machine" "Turing-machines"]
of a flavor as described in this introduction.

@note{@elemtag["Hopcroft&Ullman"]{
John E. Hopcroft and Jeffrey D. Ullman provide a comprehensive description
of Turing-machines in chapter 6 of their book:
@nonbreaking{“Formal Languages and their Relation to Automata”},
@nonbreaking{Addison-Wesley} 1969 @nonbreaking{(ISBN 0-201-0298 3-9)}.}}

A Turing-machine consists of a control-unit, a tape, a tape-head and@(linebreak)
a bidirectional data-bus between the control-unit and the tape-head.

@inset{@elemtag["figure" @image["make-TM.jpg"]]}

At every moment the control-unit has one out of a finite set of internal states.
The tape has a finite number of cells,
but can stepwise grow in both directions without limitation.
Each cell contains one out of a finite set of tape-symbols.
Together the cells form the tape-content.
The data-bus transports one tape-symbol at a time.
The first cell is considered to be at the left,
the last one to be at the right.
In the @elemref["figure" "figure above"] they are blue.
The current cell (red) is the one below the tape-head and
contains the current tape-symbol.
@elemtag["configuration"]{
The configuration of a Turing-machine is its state as a whole,
including the internal state of the control-unit,
the current tape-content and the current position of the tape-head.}

A Turing-machine must be given an input for the initial tape-content.
The input must be a finite list of non-blank tape-symbols.
The blank is a special tape-symbol used to indicate that a cell is empty.
The Turing-machine starts with a given initial internal state for the control-unit
and with the tape-head positioned at the begin of the initial tape-content.
If the input is not empty, the initial tape-content has no empty cell.
If the input is empty, the initial tape-content consists of one single empty cell.
The control-unit makes moves according to a finite set of rules.
The rule to be applied is determined by the internal state of the control-unit
and the current tape-symbol. @nonbreaking{A move} consists of three steps:

@inset{@itemlist[#:style 'ordered
          
@item{Optionally writing a non-blank tape-symbol in the current cell of the tape.
This step is not optional when the cell is empty.}

@item{@elemtag["blank"]{Optionally moving the tape-head one cell to the right or to the left.
When the tape-head moves left of the begin of the tape-content or right of the end,
an empty cell is added. This cell becomes the current one.
In this way a tape is simulated with an infinite number of
empty cells both at the left and at the right of the actual content.
However, the tape-content proper never contains more than one empty cell.
If it has an empty cell,
it is the first or the last one and it is the current one.
When the tape-head reads from the empty cell,
it sends a blank to the control unit, for it must send something.
The empty cell will be filled with a non-blank tape-symbol during the next move.}}

@item{Optionally putting the control-unit in another internal state.}]}

The Turing-machine halts as soon as it assumes a final state.
If there is no matching rule, the machine halts in a stuck state.
If it never reaches a final state and never gets stuck, it runs forever,
possibly, but not necessarily, with an ever growing tape-content.

@note{In real life tape-equipment usually the tape is moving with the tape-head in fixed position.
Moving the tape-head has the same effect
as keeping it at fixed position and moving the tape in opposit direction.}

@note{The tape-head of a Turing-machine does not move while reading
from or writing into a cell.
Only after it has done its reading from and its writing into the current cell,
the tape-head is moved one cell to the right
or to the left or remains where it is as indicated by the rule being applied.}

@note{Magnetic tape-equipment of the old days
usually destroyed all data following the newly written data,
although with some effort most, but usually not all of it, could be recovered.
This equipment was not designed for replacement of part of the data in the middle of a file.
The abstract tape-unit of a Turing-machine does not have this problem.
When a tape-symbol is written into a cell,
none of the other cells is affected, nor at the left nor at the right.}

@subsection{Two simple examples}
Let's begin with a simple example of a Turing-machine.
Its states are the initial state @rack['A], the intermediate states @rack['B], @rack['C] and
@rack['D] and the final state @rack['T].
In this example a rule has the form:

@inset{@verbatim["((old-state old-tape-symbol) (new-state new-tape-symbol) move)"]}

where:

@inset{@tabular[#:sep (list (hspace 1) "=" (hspace 1))
(list
 (list @ttt{old-state} "state")
 (list @ttt{new-state} "state")
 (list @ttt{old-tape-symbol} "tape-symbol | dummy")
 (list @ttt{new-tape-symbol} "tape-symbol | dummy")
 (list @ttt{move} @(racket(or/c 'R 'L 'N))))]}

@rack['R] indicates a move of the tape-head one cell to the right,
@rack['N] no move and @rack['L] a move one cell to the left.
A rule applies when its @ttt{old-state}
equals the current state of the control-unit
and the @ttt{old-tape-symbol} equals the current tape-symbol read from the tape,
or when it is the dummy, which is not a tape-symbol, but matches every tape-symbol.
A rule whose @ttt{new-tape-symbol} is a tape-symbol indicates that the content
of the current cell must be replaced by this tape-symbol.
A rule whose @ttt{new-tape-symbol} is the dummy indicates that
the current cell must not be altered, unless it is empty,
in which case it is filled with a space,
but this does not occur in the present example.
The machine replaces the fourth element of the initial tape-content by @rack['new].

@Interaction[
(define TM
 (make-TM #:name 'first-example
  'A      (code:comment "The initial state.")
  '(T)    (code:comment "The final states, in this case one only.")
  'blank  (code:comment "Not used, but it is a required argument.")
  'space  (code:comment "Not used, but it is a required argument.")
  '_      (code:comment "The dummy.")
  (code:comment "The rules:")
  '(((A _) (B _  ) R) (code:comment "Do not modify first  tape-symbol. Move right.")
    ((B _) (C _  ) R) (code:comment "Do not modify second tape-symbol. Move right.")
    ((C _) (D _  ) R) (code:comment "Do not modify third  tape-symbol. Move right.")
    ((D _) (T new) R) (code:comment "Replace fourth tape-symbol by 'new' and halt.\n      "))))
(code:comment " ")
(TM '(This is the original tape))]

The returned values are the number of moves made, the final state and the modified tape-content.
Let's see more details in a report of the moves.
In the report the new tape-content and the position of the tape-head are shown as

@inset{@ttt{((tape-symbol ...) (current-tape-symbol tape-symbol ...))}}

representing the content

@inset{@ttt{(tape-symbol ... current-tape-symbol tape-symbol ...)}}

and indicating that the tape-head is positioned at the @ttt{current-tape-symbol}.
The control unit has two registers,
the first one for the internal state and the second one connected to the data-bus and
containing the tape-symbol read from or to be written into the current cell of the tape.
With the given input, the following Turing-machine replaces the second and the fifth tape-symbol.

@Interaction[
(define TM
 (make-TM #:name 'second-example
  'A      (code:comment "The initial state.")
  '(T)    (code:comment "The final state.")
  'blank  (code:comment "Not used.")
  'space  (code:comment "Not used.")
  '_      (code:comment "The dummy.")
  (code:comment "The rules:")
  '((code:comment "Replace 'did by 'will and continue.")
    ((A        did) (A will     ) R)
    (code:comment "Replace 'yesterday? by 'tomorrow? and halt.")
    ((A yesterday?) (T tomorrow?) N)
    (code:comment "Don't change any other tape-symbol and continue.")
    ((A          _) (A _        ) R))))
(code:comment " ")
(TM '(What did you do yesterday?) #:report 'long)]

@subsection[#:tag "Additional registers"]{Additional registers}
The control unit of a Turing-machine made by procedure @rack[make-TM]
has at least two registers,
the primary state-register and the input/output-register.
Te latter always contains the tape-symbol read from or
to be written into the current cell of the tape.
However, the control-unit can have more registers.
During a move new states and tape-symbols can be put into the registers,
possibly obtained from other registers.
For every Turing-machine with more than two registers there
is an equivalent Turing-machine with two registers only.
It always is possible, although it may be tedious, to rewrite rules with more than two registers
as a set of rules with two registers
by including the contents of the additional registers in the primary state.
For an example,
compare section @secref["Inserting symbols"] with section @secref["More registers"].
Allowing more registers is a way to simplify the description of the rules.
For example, additional registers make it easier to describe rules that move part of the content
of the tape to another position on the tape.
They also make it easier to simulate subroutines. See section @secref{Subroutine}.

@subsection{Multiple tracks/tapes}
The tape can have more than one track.
Such a tape can be simulated by using tape-symbols consisting of
tuples (e.g. lists or vectors) of as many elements as there are tracks.

@note{Tape-symbols not necessarily are symbols of Racket in the sense of predicate @rack[symbol?].
They can be arbitrary values other than keywords and the dummy.}

It is possible to simulate a Turing-machine
with more than one tape, each one with its own tape-head.
To simulate a Turing-machine with n tapes, one can use a multiple track tape with 2n tracks.
Track i+n can be used for a mark that indicates the current position in track i.
To read from or to write into track i, the mark in track i+n must first be looked for.
However, a whole tuple must be written, one element for each track,
which may complicate the program of rules.
A separate rule would be required for every feasible tuple,
which may lead to a large number of rules.

Another way to simulate multiple tapes is to place their contents one after another in sections
with separators between them.
The separators must be tape-symbols that do not occur within the sections, of course.
In each section one symbol should be marked as the current one within that section.
A variation of this method is used in section @secref["UTM"].
By deletion or insertion of separators the machine can even vary the number of sections
while it is running.
An individual section can grow by moving all cells at the left/right one or more cells to the
left/right. In a similar way it is possible to remove part or all of a section.

@section{Procedure make-TM}
@defform-remove-empty-lines[@defform[#:kind "procedure" #:id make-TM
(make-TM initial-state final-states blank space dummy rules
          [#:registers registers #:name name])
#:grammar(
(initial-state   state)
(final-states    (final-state ...))
(blank           tape-symbol)
(space           tape-symbol)
(rules           (rule ...))
(registers       (code:line @#,element["roman"]{default =} 2)
                 (code:line (register-name register-name register-name @#,(elem
                                                                           (list (ttt "...")))))
                 (code:line @#,(racket (and/c exact-integer? (>=/c 2)))))
(name            (code:line @#,(element "roman" "default =") @#,(racket 'TM-without-name))
                 (code:line @#,(rack symbol?)))
(final-state     state)
(rule            (selector updater move))
(selector        (old-state old-symbol))
(updater         (new-state new-symbol register ...))
(old-state       state)
(old-symbol      tape-symbol dummy)
(new-state       state dummy register-name)
(new-symbol      tape-symbol dummy register-name)
(register        new-state new-symbol)
(state           (code:line @#,(racket (not/c (or/c dummy keyword?)))))
(tape-symbol     (code:line @#,(racket (not/c (or/c dummy keyword?)))))
(dummy           (code:line @#,(racket (not/c keyword?))))
(register-name   (code:line @#,(racket keyword?)))
(move            (code:line @#,(racket (or/c 'R 'L 'N)))))]{
Procedure @rack[make-TM] returns a procedure that emulates a Turing-machine.

Registers are identified by keywords.
Providing@(linebreak)@(hspace 5)
@nonbreaking{@rack[#:registers n]}@(linebreak)
with @racketlink[exact-integer? "exact integer"] @ttt{n≥2} is the same as providing:
@(linebreak)@(hspace 5)
@nonbreaking{@rack[#:registers (for/list ((k (in-range n))) (string->keyword (~s k)))]}
@(linebreak)For example,
@(linebreak)@(hspace 5)@nonbreaking{@rack[#:registers]@(hspace 1)@rack[3]}
@(linebreak)does the same as:
@(linebreak)@(hspace 5)@nonbreaking{@rack[#:registers]@(hspace 1)@rack['(#:0 #:1 #:2)]}
@(linebreak)
The first @rack[register-name] is for the primary state-register and the second one
for the input/output-register.

Before the Turing-machine is produced the arguments are checked to satisfy all contracts
and the following conditions,
equality or being distinct to be understood in the sense of @rack[equal?].
When not all of these conditions are satisfied,
procedure @rack[make-TM] raises an @rack[error].

@inset{@itemlist[#:style 'ordered
@item{The @rack[space], the @rack[blank] and the @rack[dummy] must be distinct.}
@item{The list of @rack[final-states] must not contain duplicates.}
@item{The list of @rack[final-states] must not contain any @rack[old-state].}
@item{The @rack[rules] must have distinct @rack[selector]s (the machine must be deterministic)}
@item{All @rack[register-name]s must be distinct.}
@item{Every @rack[updater] must have as many elements as there are @rack[registers].}
@item{Every keyword in an @rack[updater] must be one of the @rack[register-name]s.}]}

The @rack[name] is attached to the returned procedure
by means of Racket's procedure @rack[procedure-rename].
The @rack[name] is used in error-messages and when printing a report.

The set of @rack[state]s and the set of @rack[tape-symbol]s are not required to be disjunct.

@section{Running a Turing-machine}
The control-unit interprets the @rack[rules] as follows,
equality again to be understood in the sense of @rack[equal?].
The first @rack[register] will be referred to as the primary state-register
and its content as the primary state.
The second @rack[register] is the input/output-register.
It contains the @rack[tape-symbol] read from or to be written into
the cell currently under the tape-head.

@inset{@itemlist[#:style 'ordered
@item{A Turing-machine halts if the primary state equals one of the @rack[final-states],
      else it continues with the following steps.}

@item{The current @rack[tape-symbol] is read and put into the input/output-register.@(linebreak)
      The tape-head does not move during this step.
      If the current cell is empty, the input/output-register receives a @rack[blank].}

@item{A @rack[rule] is looked for.
A @rack[rule] applies if its @rack[old-state] equals the current primary state
and the @rack[old-symbol] matches the current @rack[tape-symbol] in the input/output-register.
The @rack[dummy] matches every @rack[tape-symbol].
Every other @rack[old-symbol] matches only when equal to the current @rack[tape-symbol].
A @rack[rule] whose @rack[old-symbol] equals the current @rack[tape-symbol]
prevails over a @rack[rule] with the same @rack[old-state] and
whose @rack[old-symbol] is the @rack[dummy].
For @rack[rules] with the same @rack[old-state] the @rack[dummy]
is like @rack[else] in a @rack[cond]- or @rack[case]-form,
but is not required to be at the end.
The order of the @rack[rules] is irrelevant.
When there is no matching @rack[rule]
the Turing-machine halts in a stuck state by raising an @rack[error].
Because procedure @rack[make-TM] checks that the @rack[selector]s of the @rack[rules] are distinct,
there can never be more than one applying @rack[rule]
(the Turing-machine is deterministic)}

@item{The registers are updated.
The element with index k of the @rack[updater]
of the @rack[rule] indicates what to put in register k.
Let x be element k of the @rack[updater].

∘ If x is the @rack[dummy] register k remains unaffected.@(linebreak)
∘ If x is a @rack[register-name] the old content of the register is put into register k.
@(linebreak)
∘ If x is a @rack[state] or a @rack[tape-symbol], it is put into register k.

For example, assuming there are three registers declared as
@rack[#:registers '(#:state #:data-bus #:extra)],
then the @rack[updater] @rack[(new-state #:extra #:data-bus)] indicates that
register @rack[#:state] is filled with @rack[new-state] and the registers @rack[#:data-bus]
and @rack[#:extra] exchange their content.
@rack[new-state] will be the new primary state and
the old content of register @rack[#:extra], which becomes the new content of register
@rack[#:data-bus], will be written into the current cell of the tape as described in the next item.}

@item{Now the @rack[tape-symbol] of the input/output-register is written in the current cell
of the tape, replacing the former current @rack[tape-symbol].
During this step the tape-head does not move.
The written @rack[tape-symbol] can be the same as the one already present in the current cell.
When the input/output-register contains a @rack[blank], a @rack[space] is written.}

@item{Finally the tape-head may be moved:@(linebreak)
@rack[move] @rack['L] : move the tape-head one cell to the left.@(linebreak)
@rack[move] @rack['R] : move the tape-head one cell to the right.@(linebreak)
@rack[move] @rack['N] : don't move the tape-head.@(linebreak)
When the tape-head moves to the left of the left-most cell of the tape or to the right of
the right-most cell,
an empty cell is added and the tape-head is positioned at this cell.}

@item{The above process is repeated until the primary state equals a @rack[final-state]
      or the Turing-machine gets stuck because
      it has no @rack[rule] matching the current primary state
      and the current @rack[tape-symbol].}]}

A procedure returned by procedure @rack[make-TM],
say @(bold (element 'tt (larger (bold "Turing-machine")))),
can be called as follows:

@defproc[#:link-target? #f
(Turing-machine
 (input (and/c (listof tape-symbol) (not/c (member blank input))))
 (#:registers register-values (or/c (listof (or/c tape-symbol state)) #f) #f)
 (#:report report (or/c boolean? 'long 'short) #f)
 (#:limit limit (or/c exact-positive-integer? #f) #f))
(values (nr-of-moves exact-nonnegative-integer?)
        final-state
        (output (listof tape-symbol)))]{
The @rack[output] is the final tape-content but without heading or trailing
@rack[blank] or @rack[space]s.
It can contain @rack[space]s, but not at the begin nor at the end.
It never contains a @rack[blank].

If @rack[register-values] is @rack[#f] all @rack[registers] are initialized with the
@rack[blank], the primary state-register excepted, which is initialized with the
@rack[initial-state]. Otherwise @rack[register-values] must be a list of as many @rack[state]s
and/or @rack[tape-symbol]s as the Turing-machine has @rack[registers] and the
@rack[register-values] provide the initial values.

@elemtag["report" ""]If @rack[report] is @rack[#t] or @rack['long] the Turing-machine
prints a long record of the moves it makes (on the @racket[current-output-port])
For each move the report shows:

@inset{@itemlist[#:style 'ordered
@item{The move counter, starting from 1.}
@item{The @rack[rule] being applied.}
@item{The original and new contents of the @rack[registers],
      the original content of the input/output-register showing the read @rack[tape-symbol],
      the new content showing the @rack[tape-symbol] to be written.}
@item{The new position of the tape-head and the new tape-content shown as
@nonbreaking{@ttt{((h ...) (c t ...))}},
where the new position of the tape-head is at @rack[tape-symbol] @ttt{c}.}]}

If @rack[report] is @rack['short] the Turing-machine
prints a short record of the moves it makes (on the @racket[current-output-port])
For each move the report shows one line containing the move-counter,
the old and new primary state, the new tape-content and the new position of the tape-head.

If @rack[report] is @rack[#f], which is the default value, no report is written.

When @rack[limit] is an @racketlink[exact-positive-integer? "exact positive integer"]
the Turing-machine halts by raising an error
when no @rack[final-state] is encountered within @rack[limit] moves.
When @rack[limit] is @rack[#f] and the Turing-machine never reaches a @rack[final-state],
the procedure keeps running forever,
unless it halts with an error because it cannot find an applying @rack[rule]
or runs out of memory because of an ever growing tape-content.

@note{An abstract Turing-machine has an infinite tape and cannot run out of memory.}
                                                 
@note{A Turing-machine returned by procedure @rack[make-TM] may,
but does not necessarily limit the input to a predefined set of @rack[tape-symbol]s.
It can use the union of the set of @rack[tape-symbol]s in the @rack[input] and
those that can be extracted from the @rack[rules] given to procedure @rack[make-TM].
At the moment the procedure that emulates the Turing-machine is called
we have a well defined finite set of @rack[tape-symbol]s.}

@note{The @rack[dummy] allows a finite multitude of regular @rack[rule]s to be written
as one single @rack[rule].
When the set of @rack[tape-symbol]s allowed in the initial tape-content is known,
every @rack[rule] whose @rack[old-symbol] is the @rack[dummy]
can be written as a finite collection of @rack[rule]s without @rack[dummy]s.}

@section{Halting problem}
Many Turing-machines never halt.
Sometimes this can be predicted by looking at the @rack[rules] only,
sometimes by inspection of both the @rack[rules] and the @rack[input].
However, because of the
@hyperlink["https://en.wikipedia.org/wiki/Halting_problem"]{Halting Problem}
there always remain cases for which it is impossible to
decide whether or not the Turing-machine will halt.
Procedure @rack[make-TM] and the Turing-machines it produces
do no checks at all against infinite loops.
Argument @rack[limit] provides protection.
The following trivial Turing-machine obviously would loop forever with
arbitrary @rack[input] if it would not be halted by the @rack[limit]:

@Interaction[
(define TM (make-TM
            'A   (code:comment "initial state")
            '()  (code:comment "no final states")
            'B   (code:comment "blank")
            'S   (code:comment "space")
            '_   (code:comment "dummy")
            '(((A _) (A S) N))
            #:name 'Non-halting-TM))
(TM '() #:report 'short #:limit 5)]

In this example @rack[rule] @rack['(((A _) (A S) N))] alone already implies an infinite loop.
While @rack[TM] is running,
its @elemref["configuration" "configuration"] never changes after the first move.
As another example consider:

@Interaction[
(define TM (make-TM
            'A     (code:comment "initial state")
            '()    (code:comment "no final state")
            'B     (code:comment "blank")
            'S     (code:comment "space")
            '_     (code:comment "dummy")
            '(((A _) (B 1) R)
              ((B _) (A 0) R))
            #:name 'Another-non-halting-TM))
(code:comment " ")
(TM '() #:report 'short #:limit 9)]

It is obvious that the above Turing-machine, no matter its initial tape-content, never halts,
although it never reproduces the same @elemref["configuration" "configuration"].
Halting or not may depend on the initial tape-content.
For example, the following Turing-machine halts only when its @rack[input]
contains @rack[tape-symbol] @rack[0].

@Interaction[
(define TM (make-TM #:name 'TM-does-it-halt?
            'A     (code:comment "initial state")
            '(T)   (code:comment "Final state")
            'B     (code:comment "blank")
            'S     (code:comment "space")
            '_     (code:comment "dummy")
            '(((A 0) (T 0) N)
              ((A _) (A _) R))))
(code:comment " ")
(code:line (TM '(3 2 1 0 1 2 3)) (code:comment "Halts."))
(code:comment " ")
(code:line (TM '(3 2 1 2 3) #:limit 9) (code:comment "Never halts."))]}}]

@section{Examples}

In the examples @rack['B] usually is the blank, @rack['S] the space and @rack['_] the dummy.
Usually @rack['T] is the final state for an accepted input and @rack['F] for a rejected input.

@note{Many of the examples are inspired by material of Jay McCarthy
that can be found in @hyperlink["http://jeapostrophe.github.io/2013-10-29-tmadd-post.html"
                                "http://jeapostrophe.github.io/2013-10-29-tmadd-post.html"].}

@subsection{Blank → space}

When a rule instructs to write a blank, in fact a space is written:

@Interaction[
(define TM
 (make-TM 'A '(T) 'blank 'space 'dummy
 '(((A blank) (B x) R)
   ((B blank) (C blank) R) (code:comment "A space is written.")
   ((C blank) (T y) N))
  #:name 'TM:blank->space))
(TM '() #:report 'long)]

@subsection{List-ref}
The following Turing-machine expects as input @ttt{(1 ... / tape-symbol ...)}.
Let k be the number of ones before the slash.
The Turing-machine halts in state @rack[T] after replacing all non-spaces by spaces,
the one with index k in the list @ttt{(tape-symbol ...+)} excepted.
Spaces in this list do not count for the index.
If there are less than k+1 non-spaces,
the Turing-machine halts in state @rack[F] with empty tape,
id est, consisting of spaces only.

@Interaction[
(define rules
(code:comment "B is the blank, S the space and _ the dummy.")
'(((A 1) (B S) R) (code:comment "Go erase the first non-space.")
  ((A /) (G S) R) (code:comment "Go erase all following the first non-space.")
  ((B 1) (B 1) R) (code:comment "Skip to the right of the slash following the ones.")
  ((B /) (C /) R)
  ((C S) (C _) R) (code:comment "Go erase first non-space at the right.")
  ((C B) (I S) L) (code:comment "Error, no non-space with index k found.")
  ((C _) (D S) L) (code:comment "Non-space found, erase it by replacing it by a space.")
  ((D _) (D _) L) (code:comment "Rewind the tape.")
  ((D /) (E /) L)
  ((E 1) (E 1) L)
  ((E S) (A S) R) (code:comment "We are at the begin of the tape. Repeat.")
  (code:comment "Index is zero or has been decreased to zero.")
  (code:comment "Erase all following the first non-space.")
  (code:comment "All preceding the non-space we are looking for,")
  (code:comment "already has been erased.")
  ((G S) (G S) R) (code:comment "Keep looking for first non-space.")
  ((G _) (H _) R) (code:comment "Found the non-space.")
  ((G B) (I S) N) (code:comment "Error, no non-space found")
  ((H _) (H S) R) (code:comment "Erase all following the non-space.")
  ((H B) (T S) N) (code:comment "Done.")
  ((I B) (F S) N) (code:comment "Error case.")
  ((I _) (I S) L) (code:comment "Erase the tape and halt in state F.\n   ")))
(code:comment " ")
(define TM
 (make-TM
  'A     (code:comment "Initial state.")
  '(T F) (code:comment "Final states.")
  'B     (code:comment "Blank")
  'S     (code:comment "Space")
  '_     (code:comment "Dummy")
  rules
  #:name 'list-ref-TM))
(code:comment " ")
(TM '(1 1 1 / a b c d e f))
(code:comment " ")
(define input '(a S b S c S d S e S f S))
(code:comment " ")
(for ((k (in-range 0 10)))
 (define-values (nr-of-moves final-state output)
  (TM (append (make-list k 1) '(/) input)))
 (printf "k=~s, nr-of-moves=~s, final-state=~s, tape=~s~n"
  k nr-of-moves final-state output))
(code:comment " ")
(code:comment "The TM is not confused when one or more of the tape-symbols are slashes.")
(code:comment " ")
(TM '(1 1 1 / / / / 1 / / /))]

@subsection{Remove symbols}
The following Turing-machine always halts.
A correct input is a list of which every element is an @rack['*] or a @rack['+].
The result of a correct input is the input without the plus-signs.
This is like addition of zero, one or more natural numbers,
where natural number k is written as `@ttt["* ..."]' with k stars.
The Turing-machine never moves left of the begin of the input.

@Interaction[
(define rules
'((code:comment "State 0 : Inspect the very first cell.")
  (code:comment "          Mark start * with x or start + with p.")
  (code:comment "          This way we can detect the begin of the input")
  (code:comment "          when moving left and avoid moving left")
  (code:comment "          of the begin of the input.")
  ((0 *) (1 x) R) (code:comment "Ok, go check the remainder of the input.")
  ((0 +) (1 p) R) (code:comment "Ok, go check the remainder of the input.")
  ((0 B) (T S) N) (code:comment "Empty input accepted.")
  ((0 _) (F _) N) (code:comment "Reject incorrect input.")
  (code:comment "State 1 : Check the remainder of the input.")
  ((1 *) (1 *) R) (code:comment "Ok, continue the check.")
  ((1 +) (1 +) R) (code:comment "Ok, continue the check.")
  ((1 B) (2 S) L) (code:comment "Input is ok. Start the addition.")
  ((1 _) (F _) N) (code:comment "Reject incorrect input.")
  (code:comment "State 2 : Do the addition from right to left.")
  (code:comment "          When entering state 2 the tape-head is at")
  (code:comment "          the right-most cell that is not a space.")
  ((2 *) (2 *) L) (code:comment "Leave * as it is and continue addition.")
  ((2 x) (T *) N) (code:comment "Start of input reached. No + encountered. Done.")
  ((2 +) (3 *) R) (code:comment "Replace + by * and replace last * by a space.")
  ((2 p) (T S) R) (code:comment "Start of input. Replace p by a space and ready.")
  (code:comment "State 3 : Go to end of tape. The current tape-symbol")
  (code:comment "          is not a + and has no +s at its right.")
  ((3 *) (3 *) R) (code:comment "Keep looking for end of input.")
  ((3 S) (4 S) L) (code:comment "End of input reached.")
  (code:comment "State 4 : Replace the last * by a space and continue addition.")
  (code:comment "          The current tape-symbol is guaranteed to be an *.")
  ((4 *) (2 S) L)))
(code:comment " ")
(define TM (make-TM #:name 'remove-plus-signs
            '0     (code:comment "initial state")
            '(T F) (code:comment "final states")
            'B     (code:comment "blank")
            'S     (code:comment "space")
            '_     (code:comment "dummy")
            rules))
(code:comment " ")
(TM '(* + * * + * * *))
(code:comment " ")
(code:comment "Let's test this TM:")
(code:comment " ")
(random-seed 0)
(for/and ((n* (in-range 0 10)))
 (define expected (make-list n* '*))
 (for/and ((n+ (in-range 0 10)))
  (define input (append expected (make-list n+ '+)))
  (for/and ((k (in-range 0 100)))
   (define-values (nr-of-moves final-state output)
    (TM (shuffle input)))
   (and (eq? final-state 'T) (equal? output expected)))))
(code:comment "What happens with empty input?")
(TM '())
(code:comment "What happens with stars only?")
(TM '(* * *))
(code:comment "What happens with plusses only?")
(TM '(+ + +))]

@subsection{Binary addition}
The following Turing-machine adds two natural numbers written in binary notation.
The Turing-machine halts with every arbitrary input.
A correct input is defined as follows:

@inset{@verbatim[
"input   := (operand + operand)
operand := bit ...+
bit     := 0 | 1"]}

An incorrect input yields final state @rack['F].
A correct input yields final state @rack['T] and @ttt{output}
@nonbreaking{@rack[(bit ...+)]}
showing the sum of the two operands.
More precisely the @ttt{output} is @nonbreaking{@rack[(1 bit ...)]} or @rack[(0)],
id est, without leading zeros.
The initial tape-content is modified such as to result in the sum.
In the sum a 0 bit is written as @element['tt "x"] and a 1 bit as @element['tt "y"]
such as to know which bits already have been established and which ones yet have to be computed.
During the addition the tape-content is (ignoring spaces and blank) 
@nonbreaking{@element['tt "(0-or-1 ... x-or-y ... + 0-or-1 ...)"]},
where @rack[x] represents a computed 0 and @rack[y] a computed 1.
The refrasing in @rack[x] and @rack[y] is necessary in order to know
which part of the sum already has been established and to which part of the
remaining zeros and ones of the first operand each next bit of the first operand must be added.
Bits of the second operand are processed starting from the least significant one.
Every such bit is replaced by a space before it is processed.
The significance of this bit is the same as that of
the right-most bit @nonbreaking{@element['tt "0-or-1"]} of the first operand.
After all bits of the second operand have been processed,
the @element['tt "+"] is removed,
tape-symbols @element['tt "x"] and @element['tt "y"] are reverted to
@rack[0] and @rack[1] and leading zeros are removed.

@Interaction[
(define rules
'((code:comment "Check the input.")
  (code:comment "At least one bit required preceding +.")
  ((0 0) (1 0) R) (code:comment "Ok, continue parsing the first operand.")
  ((0 1) (1 1) R) (code:comment "Ok, continue parsing the first operand.")
  ((0 _) (F _) N) (code:comment "Reject.")
  (code:comment "Check the remainder of the first operand.")
  ((1 0) (1 0) R) (code:comment "Continue checking the first operand.")
  ((1 1) (1 1) R) (code:comment "Continue checking the first operand.")
  ((1 +) (2 +) R) (code:comment "End of first operand, go to second operand.")
  ((1 _) (F _) N) (code:comment "Reject.")
  (code:comment "At least one bit required for the second operand.")
  ((2 0) (3 0) R) (code:comment "Ok, continue parsing the second operand.")
  ((2 1) (3 1) R) (code:comment "Ok, continue parsing the second operand.")
  ((2 _) (F _) N) (code:comment "Reject.")
  (code:comment "Check the remainder of the second operand.")
  ((3 0) (3 0) R) (code:comment "Ok, continue parsing the second operand.")
  ((3 1) (3 1) R) (code:comment "Ok, continue parsing the second operand.")
  ((3 B) (4 S) L) (code:comment "End of correct input. Go to the addition.")
  ((3 _) (F _) N) (code:comment "Reject.")
  (code:comment "Addition")
  (code:comment "We are at the least significant bit of the second operand.")
  ((4 0) (5 S) L) (code:comment "Erase the bit and add it to the first operand.")
  ((4 1) (7 S) L) (code:comment "Erase the bit and add it to the first operand.")
  (code:comment "Adding bit 0.")
  (code:comment "Look for the least significant bit of the first operand.")
  ((5 +) (6 +) L) (code:comment "Least significant bit of first operand found.")
  ((5 _) (5 _) L) (code:comment "Continue looking for first operand.")
  ((6 x) (6 x) L) (code:comment "Skip bits already computed.")
  ((6 y) (6 y) L) (code:comment "Skip bits already computed.")
  ((6 0) (A x) R) (code:comment "Mark bit as having been computed.")
  ((6 1) (A y) R) (code:comment "Mark bit as having been computed.")
  ((6 B) (A x) R) (code:comment "Add a bit marked as having been computed.")
  ((6 S) (A x) R) (code:comment "Add a bit marked as having been computed.")
  (code:comment "Adding bit 1.")
  (code:comment "Look for the least significant bit of the first operand.")
  ((7 +) (8 +) L) (code:comment "Least significant bit of first operand found.")
  ((7 _) (7 _) L) (code:comment "Continue looking for first operand.")
  ((8 x) (8 x) L) (code:comment "Skip bits already computed.")
  ((8 y) (8 y) L) (code:comment "Skip bits already computed.")
  ((8 0) (A y) R) (code:comment "Put a 1 bit as having been computed.")
  ((8 1) (9 x) L) (code:comment "Put a zero bit as being computed and process carry.")
  ((8 S) (A y) R) (code:comment "Add the bit.")
  ((8 B) (A y) R) (code:comment "Add the bit.")
  (code:comment "Process a carry.")
  ((9 0) (A 1) R)
  ((9 1) (9 0) L)
  ((9 S) (A 1) R)
  ((9 B) (A 1) R)
  (code:comment "Go to next least significant bit of second operand.")
  ((A S) (B S) L) (code:comment "End of second operand.")
  ((A _) (A _) R) (code:comment "Keep on looking.")
  (code:comment "Here we are at the least significant bit of the second operand.")
  ((B 0) (5 S) L) (code:comment "Remove bit from the second operand and go add it.")
  ((B 1) (7 S) L) (code:comment "Remove bit from the second operand and go add it.")
  ((B +) (C S) L) (code:comment "Second operand totaly processed. Erase the + sign.")
  (code:comment "Addition is complete.")
  (code:comment "Revert x to 0 and y to 1.")
  ((C x) (C 0) L)
  ((C y) (C 1) L)
  ((C 0) (C 0) L)
  ((C 1) (C 1) L)
  ((C S) (D S) R)
  ((C B) (D S) R)
  (code:comment "Remove heading zeros, but make sure at least one bit remains.")
  ((D 0) (D S) R)
  ((D 1) (T 1) N)
  ((D S) (T 0) N)
  ((D B) (T 0) N)))
(code:comment " ")
(define adder (make-TM #:name 'binary-addition
               '0     (code:comment "initial state")
               '(T F) (code:comment "final states")
               'B     (code:comment "blank")
               'S     (code:comment "space")
               '_     (code:comment "dummy")
               rules))
(code:comment " ")
(adder '(1 0 1 1 + 1 0 1 1 1))
(code:comment " ")
(adder '(0 1 1 + 0 0 0 1 1))
(code:comment " ")
(adder '(0 0 0 + 0 0))
(code:comment " ")
(code:comment "Testing the TM.")
(code:comment "We need two procedures for conversion between")
(code:comment "exact nonnegative integer numbers and lists of bits.")
(code:comment " ")
(code:comment "Procedure exact-nonnegative-integer->list-of-bits converts")
(code:comment "an exact nonnegative integer to a list of bits 0 and 1.")
(code:comment " ")
(define (exact-nonnegative-integer->list-of-bits n)
 (if (zero? n) '(0)
  (let loop ((n n) (r '()))
   (cond
    ((zero? n) r)
    ((even? n) (loop (quotient n 2) (cons 0 r)))
    (else      (loop (quotient n 2) (cons 1 r)))))))
(code:comment " ")
(code:comment "Procedure list-of-bits->exact-nonnegative-integer converts")
(code:comment "a list of bits 0 and 1 to an exact nonnegative integer.")
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
 (define n (random 30000000))
 (= n
  (list-of-bits->exact-nonnegative-integer
   (exact-nonnegative-integer->list-of-bits n))))
(code:comment " ")
(code:comment "Test the TM.")
(code:comment " ")
(for/and ((k (in-range 0 100)))
 (define n (random 30000000))
 (define m (random 30000000))
 (define input
  (append
   (exact-nonnegative-integer->list-of-bits n)
   (list '+)
   (exact-nonnegative-integer->list-of-bits m)))
 (define-values (nr-of-moves final-state output) (adder input))
 (and (eq? final-state 'T)
  (= (list-of-bits->exact-nonnegative-integer output) (+ n m))))]

@subsection{Decimal addition}
The following Turing-machine expects @nonbreaking{@element['tt "((n m) ...)"]} as input,
where each @element['tt "n"] and each @element['tt "m"] is a decimal digit coded as
an exact integer between 0 (inclusive) and 10 (exclusive).
The Turing-machine adds the numbers @element['tt "n..."] and @element['tt "m..."] and
returns the sum @element['tt "s..."].
The machine first passes to the end of the input.
Subsequently it does the addition in one pass to the left
going from the least to the most significant digit.
Redundant heading zeros are not removed.
It replaces each tape-symbol @nonbreaking{@element['tt "(n m)"]} by one decimal digit.
State @rack[0] indicates that there is no carry.
State @rack[1] indicates that a carry must be added.
State @rack['A] is the initial internal state and @rack['T] the final state.
The initial tape-content seems a tape of two tracks,
but it is replaced by a tape of one track only.

@Interaction[
(define rules
 (append
  (list
   '((A _) (A _) R) (code:comment "First go to the right.")
   '((A B) (0 S) L)
   '((0 B) (T 0) N) (code:comment "All done.")
   '((1 B) (T 1) N))
  (for*/list
   ((c (in-range 0 2))   (code:comment "0 = no carry, 1 = carry")
    (n (in-range 0 10))  (code:comment "digit of first operand")
    (m (in-range 0 10))) (code:comment "digit of second operand")
   (define-values (q r) (quotient/remainder (+ n m c) 10))
   `((,c (,n ,m)) (,q ,r) L))))
(code:comment " ")
(begin (printf " ~nThe rules:~n ~n")
 (for ((rule (in-list rules)) (nl (in-cycle '(#f #f #f #t))))
  (printf (if nl "~a~n" "~a ") (~s #:width 19 #:min-width 19 rule))))
(code:comment " ")
(define TM (make-TM #:name 'decimal-addition
            'A   (code:comment "initial state")
            '(T) (code:comment "final state")
            'B   (code:comment "blank")
            'S   (code:comment "space")
            '_   (code:comment "dummy")
            rules))
(code:comment " ")
(TM '((0 0) (0 0) (9 9) (0 0) (0 0) (9 9) (9 9)) #:report 'short)
(code:comment " ")
(code:comment "nr->lst takes an exact nonnegative integer and")
(code:comment "returns its list of digits.")
(code:comment " ")
(define (nr->lst n)
 (define (nr->lst n result)
  (cond
   ((zero? n) result)
   (else
    (define-values (q r) (quotient/remainder n 10))
    (nr->lst q (cons r result)))))
 (if (zero? n) '(0) (nr->lst n '())))
(code:comment " ")
(code:comment "prepare-input takes two exact nonnegative integers")
(code:comment "and returns the corresponding input for TM.")
(code:comment " ")
(define (prepare-input n m)
 (let ((n (nr->lst n)) (m (nr->lst m)))
  (define ln (length n))
  (define lm (length m))
  (define len (max ln lm))
  (map list (append (make-list (- len ln) 0) n)
            (append (make-list (- len lm) 0) m))))
(code:comment " ")
(code:comment "output->nr converts the output of the TM")
(code:comment "to an exact nonnegative integer.")
(code:comment " ")
(define (output->nr lst)
 (define (output->nr lst)
  (if (null? lst) 0
   (+ (car lst) (* 10 (output->nr (cdr lst))))))
 (output->nr (reverse lst)))
(code:comment " ")
(let ((n 9876) (m 987654))
 (define-values (nr-of-moves final-state output)
  (TM (prepare-input n m) #:report 'long))
 (define sum (output->nr output))
 (values sum (= sum (+ n m))))
(code:comment " ")
(code:comment "Test the TM.")
(code:comment " ")
(for/and ((k (in-range 0 1000)))
 (define n (random 1000000000))
 (define m (random 1000000000))
 (define-values (nr-of-moves final-state output)
  (TM (prepare-input n m)))
 (and (= (output->nr output) (+ n m)) (eq? final-state 'T)))]

@subsection{@hyperlink["https://en.wikipedia.org/wiki/Busy_beaver" "Busy beaver"]}
@subsubsub*section{@larger{@larger{Three state busy beaver}}}
In fact there are four states, but final state @rack['T] does not count.

@Interaction[
(define rules
 '(((A 0) (C 1) R)
   ((A 1) (A 1) R)
   ((B 0) (A 1) R)
   ((B 1) (C 1) L)
   ((C 0) (B 1) L)
   ((C 1) (T 1) N)))
(define BB3
 (make-TM #:name 'BB3
  'A   (code:comment "The initial state.")
  '(T) (code:comment "The final state.")
  0    (code:comment "The blank.")
  'space-not-used
  'dummy-not-used
  rules))
(BB3 '() #:report 'short)]

@subsubsub*section{@larger{@larger{Four state busy beaver}}}
In fact there are five states, but final state @rack['T] does not count.
For every non-final state @rack[old-state] there are two rules,
@rack[((old-state _) (new-state 1) move)] and
@rack[((old-state 1) (new-state 0-or-1) move)].
This implies that a blank @rack['B] and tape-symbol @rack[0] always
are treated in the same way whenever encountered as the current tape-symbol.
This removes the distinction between these two tape-symbols.

@Interaction[
(define rules
 '(((A _) (B 1) R)
   ((A 1) (B 1) L)
   ((B _) (A 1) L)
   ((B 1) (C 0) L)
   ((C _) (T 1) R)
   ((C 1) (D 1) L)
   ((D _) (D 1) R)
   ((D 1) (A 0) R)))
(define BB4
 (make-TM #:name 'BB4
  'A   (code:comment "The initial state.")
  '(T) (code:comment "The final state.")
  'blank
  'space
  '_   (code:comment "The dummy.")
  rules))
(BB4 '())]

@subsection["{0,1}"@superscript{*}]

The following Turing-machine halts on every arbitrary input.
If the input is a list of zeros and ones with as many zeros as ones,
the final state is @rack['T].
In all other cases the final state is @rack['F].
The Turing-machine accepts an empty input immediately.
If the input is not empty, a starting mark @rack['s] is added at the left,
the input is checked to consist of zeros and ones only
and an ending mark @rack['e] is added at the end of the input.
Now the tape-head is at the cell immediately left of the end-mark @rack['e].
The following process is repeated until halted.
Starting from the right, the Turing-machine looks at the left for a @rack[0] or a @rack[1].
If a @rack[0] is encountered, it is replaced by @rack['e] and a required @rack[1] is looked for.
If a @rack[1] is encountered, it is replaced by @rack['e] and a required @rack[0] is looked for.
After finding a required @rack[0] or @rack[1], it is replaced by @rack['S],
the tape-head is positioned at the rightmost @rack[0] or @rack[1]
and the process is repeated until there are no more @rack[0]s or @rack[1]s.
If a required @rack[0] or @rack[1] is not found, the Turing-machine halts in state @rack['F].

@Interaction[
(define rules
 '((code:comment "state 0: starting state.")
   (code:comment "Accept empty input, otherwise add starting mark s.")
   ((0 B) (T S) N) (code:comment "Accept empty input.")
   ((0 _) (1 _) L)
   ((1 B) (2 s) R)
   (code:comment "state 2: Check that we have 0s and 1s only and add an ending mark e.")
   ((2 0) (2 0) R)
   ((2 1) (2 1) R)
   ((2 B) (3 e) N)
   ((2 _) (F _) N)
   (code:comment "state 3: Go to the end of the tape (marked by one or more e's)")
   ((3 e) (4 e) L)
   ((3 _) (3 _) R)
   (code:comment "state 4: look for a 0 or a 1 at the left")
   ((4 s) (7 e) N) (code:comment "Ok, no more 0s or 1s.")
   ((4 0) (5 e) L) (code:comment "a 1 at the left is required. Mark the 0 as end of tape.")
   ((4 1) (6 e) L) (code:comment "a 0 at the left is required. Mark the 1 as end of tape.")
   ((4 S) (4 e) L)
   (code:comment "state 5: look for a required 1 at the left.")
   ((5 0) (5 0) L) (code:comment "skip 0.")
   ((5 1) (3 S) R) (code:comment "found.")
   ((5 s) (F s) N) (code:comment "no 1 found.")
   ((5 S) (5 S) L)
   (code:comment "state 6: look for a required 0 at the left.")
   ((6 0) (3 S) R) (code:comment "found.")
   ((6 1) (6 1) L) (code:comment "skip 1.")
   ((6 s) (F s) N) (code:comment "no 0 found.")
   ((6 S) (6 S) L)
   (code:comment "Erase all e's before halting in state T.")
   ((7 _) (7 S) R)
   ((7 B) (T S) N)))
(code:comment " ")
(define TM
 (make-TM #:name 'zeros-and-ones
  0      (code:comment"initial state")
  '(T F) (code:comment"final states")
  'B     (code:comment"blank")
  'S     (code:comment"space")
  '_     (code:comment"dummy")
  rules))
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
 (define expected-state (if (= n0 n1) 'T 'F))
 (for/and ((n (in-range 0 100)))
  (test (shuffle input) expected-state)))]

@subsection{Matching parentheses}

The following two Turing-machines read @rack['<] as a left parenthesis
an @rack['>] as a right parenthesis.
The Turing-machines halt in state @rack[T] if the parentheses are well balanced
and no other symbols occur in the input.
In all other cases the Turing-machines halt in state @rack[F].
The second example uses a counter.
The method used in the first example is as follows.
First check that the input consists of @rack['<] and @rack['>] only.
Put tape-symbol @rack[s] at the left of the input
and tape-symbol @rack[e] at the right.
This helps detecting the begin and the end of the current tape-content.
Starting from the right go left looking for a @rack['>]
whose first preceding non-space symbol is @rack['<].
When found replace the @rack['<] and the @rack['>]
by spaces, go to the right of the input and repeat.
When looking for a @rack['>] all symbols appear to be spaces,
the Turing-machine halts in state @rack[T].
When encountering a @rack['<] before encountering a @rack['>] the parentheses are not balanced
and the Turing-machine halts in state @rack[F].

@note{There are @nonbreaking{C@subscript{n} = (2n)!/(n!(n+1)!)}
ways to write n pairs of matching parentheses, n≥0.@(linebreak)
There are two recurrent relations starting with @nonbreaking{C@subscript{0} = 1}:@(linebreak)
@nonbreaking{C@subscript{n+1} = ((4n+2)C@subscript{n})/(n+2) =
@bold{@larger{Σ}}@subscript{(k=0@bold{:}n)}(C@subscript{k}C@subscript{n@subscript{@ttt{-}}k})}.
See @hyperlink["https://en.wikipedia.org/wiki/Catalan_number" "Catalan numbers"].}

@Interaction[
(define rules
  (code:comment "state 0")
  (code:comment "accept empty input.")
  (code:comment "put begin marker s before non-empty input.")
'(((0 B) (T S) N)
  ((0 _) (1 _) L)
  ((1 B) (2 s) R)
  (code:comment "state 2")
  (code:comment "check input.")
  (code:comment "put end marker e at end of input.")
  ((2 <) (2 <) R)
  ((2 >) (2 >) R)
  ((2 B) (3 e) L)
  ((2 _) (F _) N)
  (code:comment "state 3")
  (code:comment "we are at the end of the tape.")
  (code:comment "look left for > preceded by <.")
  ((3 S) (3 S) L)
  ((3 s) (T S) R) (code:comment "all done, accept.")
  ((3 >) (4 >) L) (code:comment "found a >.")
  ((3 <) (F <) N) (code:comment "non-matching left parenthesis.")
  ((4 S) (4 S) L)
  ((4 <) (5 S) R) (code:comment "found preceeding <, erase it with a space.")
  ((4 >) (4 >) L) (code:comment "found another >.")
  ((4 s) (F s) N) (code:comment "no matching < found.")
  (code:comment "state 5")
  (code:comment "erase the > corresponding to the < just erased.")
  ((5 >) (6 S) R)
  ((5 S) (5 S) R)
  (code:comment "state 6")
  (code:comment "go to end of tape and repeat.")
  ((6 e) (3 e) L)
  ((6 _) (6 _) R)))
(code:comment " ")
(define TM (make-TM 0 '(T F) 'B 'S '_ rules #:name 'parentheses))
(code:comment " ")
(code:comment #,(elemtag "mp" "match-parentheses does the same as the TM. Used for tests."))
(code:comment " ")
(define (match-parentheses lst)
 (define (match-parentheses lst n)
  (cond
   ((null? lst) (if (zero? n) 'T 'F))
   ((eq? (car lst) '<) (match-parentheses (cdr lst) (add1 n)))
   ((zero? n) 'F)
   (else (match-parentheses (cdr lst) (sub1 n)))))
 (match-parentheses lst 0))
(code:comment " ")
(code:comment "Test now.")
(code:comment "Try all (expt 2 k) inputs of k elements,")
(code:comment "k running from 0 to 10 (inclusive).")
(code:comment "A total of 2047 tests of which only 65 yield final state T.")
(code:comment #,(elemtag "Catalan" " "))
(define (Catalan n)
 (cond
  ((zero? n) 1)
  (else
   (define m (sub1 n))
   (/ (* (+ (* 4 m) 2) (Catalan m)) (+ m 2)))))
(code:comment " ")
(define (check k cnt)
 (define expected
  (cond
   ((odd? k) 0)
   (else (Catalan (quotient k 2)))))
 (unless (= cnt expected)
  (error 'parentheses "k=~s, found ~s, expected ~s" k cnt expected)))
(code:comment " ")
(for/fold ((total 0)) ((k (in-range 0 11 2)))
 (printf "~s parentheses.~n" k)
 (define counter
  (for*/fold ((cnt 0)) ((n (in-range (arithmetic-shift 1 k))))
   (define input
    (for/list ((k (in-range 0 k)))
     (if (zero? (bitwise-and (arithmetic-shift 1 k) n)) '< '>)))
   (define-values (nr-of-moves state output) (TM input))
   (unless (eq? state (match-parentheses input)) (error 'Test "test failed")) 
   (cond
    ((eq? state 'T)
     (printf "~a ~s~n" (~s #:min-width 2 #:align 'right (add1 cnt)) input)
     (add1 cnt))
    (else cnt))))
 (check k counter)
 (+ counter total))]

When counting a @rack['<] as @element['tt "+1"] and a @rack['>] as @element['tt "-1"],
going from left to right the addition must never go below zero and must end in zero.
The following Turing-machine uses such a counter.
It is put at the end of the input between two slashes.
The counter consists of @rack[0]s and @rack[1]s,
and the number of @rack[1]s is the count.
When decreasing the counter the first @rack[1] is replaced by a @rack[0].
If no @rack[1] can be found, the parentheses do not match.
When increasing the counter the first @rack[0] is replaced by a @rack[1],
or, if no @rack[0] can be found, a @rack[1] is added at the end.
After all parentheses have been processed,
the counter is checked to be zero.

@Interaction[
(define rules
'(
  (code:comment "Check the input.")
  ((1 B) (2 /) R) (code:comment "Input ok.")
  ((1 >) (1 >) R) (code:comment "Ok, continue.")
  ((1 <) (1 <) R) (code:comment "Ok, continue.")
  ((1 _) (F _) N) (code:comment "Reject.")
  (code:comment "Initialize counter at end of input.")
  ((2 B) (3 /) L)
  (code:comment "Go to the left of the input.")
  ((3 B) (4 S) R)
  ((3 S) (4 S) R)
  ((3 _) (3 _) L)
  (code:comment "Find parenthesis.")
  ((4 <) (5 S) R) (code:comment "Go increase counter.")
  ((4 >) (8 S) R) (code:comment "Go decrease counter.")
  ((4 /) (A /) R) (code:comment "Go check counter to be 0.")
  (code:comment "Go to the counter and add a 1")
  ((5 /) (6 /) R) (code:comment "Counter found.")
  ((5 _) (5 _) R) (code:comment "Keep looking.")
  ((6 0) (3 1) L) (code:comment "Added a 1, repeat.")
  ((6 1) (6 1) R)
  ((6 /) (7 1) R) (code:comment "Add a 1.")
  ((7 B) (3 /) L) (code:comment "and repeat.")
  (code:comment "Go to the counter and remove a 1")
  ((8 /) (9 /) R) (code:comment "Counter found.")
  ((8 _) (8 _) R) (code:comment "Keep looking.")
  ((9 1) (3 0) L) (code:comment "Removed a 1, repeat.")
  ((9 0) (9 0) R)
  ((9 /) (F /) N) (code:comment "Counter becomes negative. Wrong.")
  (code:comment "Check the counter to be zero.")
  ((A 0) (A 0) R)
  ((A 1) (F 1) N) (code:comment "Counter is not zero. Wrong.")
  ((A /) (B S) L) (code:comment "Counter is zero. OK.")
  (code:comment "Erase the counter (the parentheses already have been erased)")
  ((B _) (B S) L)
  ((B S) (T S) N)
  ((B B) (T S) N)))
(code:comment " ")
(define TM (make-TM 1 '(F T) 'B 'S '_ rules))
(code:comment " ")
(TM '(< < < > > < > >) #:report 'short)
(code:comment " ")
(code:comment "Test now.")
(code:comment " ")
(for/and ((k (in-range 0 17 2)))
 (define counter
  (for/fold ((cnt 0)) ((n (in-range (arithmetic-shift 1 k))))
   (define input
    (for/list ((k (in-range 0 k)))
     (if (zero? (bitwise-and (arithmetic-shift 1 k) n)) '< '>)))
   (define-values (nr-of-moves state output) (TM input #:report #f))
   (code:comment #,(list "match-parentheses has been defined " (elemref "mp" "above")))
   (unless (eq? state (match-parentheses input)) (error 'Test "test failed"))
   (cond
    ((eq? state 'T) (add1 cnt))
    (else cnt))))
 (code:comment #,(list "Catalan has been defined " (elemref "Catalan" "above")))
 (define ok (= counter (Catalan (/ k 2))))
 (printf "k=~s, count=~s, ok=~s~n" k counter ok)
 ok)]

@subsection[#:tag "Inserting symbols"]{Inserting symbols}

The following Turing-machine always halts.
For an input consisting of @rack['a]s and @rack['b]s only
the final state is @rack['T] and symbol @rack['x] is inserted
between each @rack['a] and an immediately following @rack['b].
The insertion of @rack['x] requires that the tape-symbols
preceding the @rack['b] are shifted one cell to the left.
An input containing anything other than @rack['a] or @rack['b]
yields final state @rack['F].
@rack[0] is the initial state.

@Interaction[
(define rules
'((code:comment "Look for a.")
  ((0     a) (1     a) R)
  ((0     b) (0     b) R)
  ((0     B) (T     S) N)
  ((0     _) (F     _) N)
  (code:comment "Symbol a found, is next symbol b?")
  ((1     a) (1     a) R) (code:comment "Keep looking for b.")
  ((1     b) (2     M) L) (code:comment "yes, mark it M and proceed.")
  ((1     _) (F     _) N)
  ((1     B) (T     S) N)
  (code:comment "Rewind the tape.")
  ((2     B) (3     S) R)
  ((2     _) (2     _) L)
  (code:comment "Shift every symbol one cell to the left up to mark M.")
  (code:comment "Replace a or b or x by S.")
  (code:comment "Replace preceding S by a or b or x.")
  (code:comment "Replace M by b and replace preceding S by x.")
  (code:comment "Memorize the symbol in the new state.")
  ((3     a) ((4 a) S) L)
  ((3     b) ((4 b) S) L)
  ((3     x) ((4 x) S) L)
  ((3     M) ((4 M) b) L)
  (((4 a) S) (5     a) R) (code:comment "Continue the shift.")
  (((4 b) S) (5     b) R) (code:comment "Continue the shift.")
  (((4 x) S) (5     x) R) (code:comment "Continue the shift.")
  (((4 M) S) (0     x) R) (code:comment "Shift completed. Look for next a followed by b.")
  (code:comment "Go to the right of the space inserted in state 3 and continue the shift.")
  ((5  S) (3  S) R)))
(code:comment " ")
(define TM (make-TM  0 '(T F) 'B 'S  '_ rules))
(code:comment " ")
(code:comment "Example:")
(code:comment " ")
(TM '(b a b a b a) #:report 'short)
(code:comment " ")
(code:comment "Let's test the TM.")
(code:comment "The following procedure does the same as the TM")
(code:comment "It is used to test the TM.")
(code:comment " ")
(define (ab->axb input)
 (cond
  ((null? input) '())
  ((null? (cdr input)) input)
  ((equal? (take input 2) '(a b))
   (append '(a x b) (ab->axb (cddr input))))
  (else (cons (car input) (ab->axb (cdr input))))))
(code:comment " ")
(random-seed 0) (code:comment "Let's do the tests now:")
(code:comment " ")
(for*/and ((na (in-range 10)) (nb (in-range 10)))
 (define ab (append (make-list na 'a) (make-list nb 'b)))
 (for/and ((k (in-range 100)))
  (define input (shuffle ab))
  (define-values (nr-of-moves state output) (TM input))
  (define expect (ab->axb input))
  (and
   (equal? output expect)
   (equal? state 'T))))]

@subsection{Counter}

Represent natural number n as @ttt{x ...} or @ttt{y ...} with n @ttt{x}s or @ttt{y}s.
The following Turing-machine never halts when given an empty input.
It forms an infinite tape containing the numbers 0, 1, 2 etc.
separated by slashes.
Every next number is formed by putting an @ttt{x} at the end of the content
and copying the previous number, which has the form @ttt{x ...}.
While copying, the @ttt{x}s of the previous number are replaced by @ttt{y}s
such as to indicate they already have been copied.

@Interaction[ 
(define rules
'((code:comment "Form zero.")
  ((0 B) (1 /) R)
  ((1 B) (2 /) R)
  (code:comment "Put an x and go add the previous nr.")
  ((2 B) (3 x) L)
  (code:comment "First go to end of previous nr.")
  ((3 /) (4 /) L)
  ((3 _) (3 _) L)
  (code:comment "Copy x to end of tape.")
  (code:comment "Copied xs are replaced by ys.")
  ((4 x) (5 y) R)   (code:comment "Mark x as copied and go put x at end of tape.")
  ((4 y) (4 y) L)   (code:comment "y has already been copied. Keep looking for x.")
  ((4 /) (6 /) R)   (code:comment "Copy is complete.")
  ((5 _) (5 _) R)   (code:comment "Go to end of tape, write x and")
  ((5 B) (3 x) L)   (code:comment "continue copying.")
  (code:comment "Next number complete.")
  ((6 _) (6 _) R)   (code:comment "Go to end of tape.")
  ((6 B) (2 /) R)   (code:comment "Go form the next nr.\n   ")))
(code:comment " ")
(define TM
 (make-TM #:name 'counter
 '0   (code:comment "initial state")
 '()  (code:comment "no final state")
 'B   (code:comment "blank")
 'space-not-used
 '_   (code:comment "dummy")
 rules))
(code:comment " ")
(code:comment "Limit the number of moves.")
(code:comment "The error message shows the resulting tape-content.")
(TM '() #:limit 162)]

The following counter is like the previous one,
but writes its numbers in binary notation and every new one at the left of the previous one.
Bits 0 and 1 are used, but the most recently computed number consists of bits o for 0 and i for 1.
Bits o and i indicate that they have not yet been copied.
Every next number is formed by copying the most recent one
while converting o and i of the original to 0 and 1.
i is added to the copy before generating the next number.

@Interaction[
(define rules
'(
  (code:comment "First form tape (/ o /).")
  ((0  B) (1  /) L) (code:comment "Write /")
  ((1  B) (2  o) L) (code:comment "Write o")
  ((2  B) (3  /) R) (code:comment "Write /")
  (code:comment "Copy the number at the begin of the tape.")
  (code:comment "Look for the least significant bit o or i.")
  ((3  /) (4  _) L) (code:comment "Position found.")
  ((3  0) (4  _) L) (code:comment "Position found.")
  ((3  1) (4  _) L) (code:comment "Position found.")
  ((3  o) (3  _) R) (code:comment "Keep looking at the right.")
  ((3  i) (3  _) R) (code:comment "Keep looking at the right")
  (code:comment "Copy the least significant bit just found.")
  ((4  /) (8  _) L) (code:comment "All copied, go add i=1 to the copy.")
  ((4  o) (5o 0) L) (code:comment "Mark as copied and go put bit o at begin of tape.")
  ((4  i) (5i 1) L) (code:comment "Mark as copied and go put bit i at begin of tape.")
  (code:comment "Go to begin of tape and write the bit memorized in state 5o or 5i")
  ((5o _) (5o _) L)
  ((5o B) (6  o) R) (code:comment "write the o.")
  ((5i _) (5i _) L)
  ((5i B) (6  i) R) (code:comment "write the i.")
  (code:comment "Go to the end of the number.")
  ((6  /) (3  _) R) (code:comment "End found. Look for the next bit to copy.")
  ((6  _) (6  _) R)
  (code:comment "Add o=0, but put / at the begin of the tape.")
  ((7  B) (3  /) R) (code:comment "Done, go for the next number.")
  ((7  o) (7  o) L)
  ((7  i) (7  i) L)
  (code:comment "Add i=1.")
  ((8  B) (9  i) L) (code:comment "Done, go write terminating /.")
  ((8  o) (7  i) L)
  ((8  i) (8  o) L)
  (code:comment "Write terminating / and go for the next number.")
  ((9  B) (3  /) R)))
(code:comment " ")
(define TM (make-TM 0 '() 'B 'S '_ rules #:name 'binary-counter))
(TM '() #:limit 139)]

@subsection[#:tag "More registers"]{More registers}
The Turing-machines shown sofar in this document have one data-register and
one state-register only.
Let us use a Turing-machine with two data-registers to simplify and to speed up
the example of section @secref{Inserting symbols}.
One extra data-register is used.
It memorizes the previously replaced symbol when shifting tape-symbols to the left
in order to make space for an x.
The registers are called @rack[#:state], @rack[#:current] and @rack[#:previous].

@Interaction[
(define rules
 '((code:comment "look for a.")
   ((0 a) (1 a          B        ) R) (code:comment "a found.")
   ((0 b) (0 b          B        ) R) (code:comment "keep looking.")
   ((0 x) (0 x          B        ) R) (code:comment "keep looking")
   ((0 B) (T S          B        ) N) (code:comment "all done, halt.")
   ((0 S) (T S          B        ) N) (code:comment "all done, halt.")
   ((0 _) (F S          B        ) N) (code:comment "disallowed input, halt.")
   (code:comment "Is a followed by b?")
   ((1 a) (1 a          B        ) R) (code:comment "no, but we have an a, hence continue.")
   ((1 b) (2 b          x        ) L) (code:comment "yes, insert x and shift cells left.")
   ((1 x) (0 x          B        ) R) (code:comment "no, go looking for an a.")
   ((1 S) (T S          B        ) N) (code:comment "end of tape, accept.")
   ((1 B) (T S          B        ) N) (code:comment "end of tape, accept.")
   ((1 _) (F S          B        ) N) (code:comment "disallowed input, halt.")
   (code:comment "Shift all cells at the left one cell to the left.")
   ((2 _) (2 #:previous #:current) L) (code:comment "Does the shift.")
   ((2 B) (0 #:previous B        ) R) (code:comment "Done, repeat the whole process.")
   ((2 S) (0 #:previous B        ) R) ))
(code:comment " ")
(define TM
 (make-TM  0 '(T F) 'B 'S  '_ rules
  #:registers '(#:state #:current #:previous)))
(code:comment " ")
(TM '(b a b a b a))
(code:comment " ")
(code:comment "Let's test the TM.")
(code:comment "The following procedure does the same as the TM.")
(code:comment "It is used to test the TM.")
(code:comment " ")
(define (ab->axb input)
 (cond
  ((null? input) '())
  ((null? (cdr input)) input)
  ((equal? (take input 2) '(a b)) (append '(a x b) (ab->axb (cddr input))))
  (else (cons (car input) (ab->axb (cdr input))))))
(code:comment " ")
(random-seed 0)
(code:comment " ")
(for*/and ((na (in-range 20)) (nb (in-range 20)))
 (define ab (append (make-list na 'a) (make-list nb 'b)))
 (for/and ((k (in-range 100)))
  (define input (shuffle ab))
  (define-values (nr-of-moves state output) (TM input))
  (define expect (ab->axb input))
  (and
   (equal? (ab->axb input) output)
   (equal? state 'T))))]

@subsection{Subroutine}
The Turing-machine below starts in state @rack[1].
The program includes a subroutine that starts with state @rack[sub0]
and wants two arguments, the state to return to and a tape-symbol to be inserted.
These arguments are put in registers @rack[#:return-state] and @rack[#:symbol-arg].
The subroutine shifts each cell one step to the right starting from the current cell,
moves back to the cell it came from,
writes the given @rack[#:symbol-arg]
and returns by entering the @rack[#:return-state].
The subroutine is called twice.
The first time with return-state @rack[3] and tape-symbol @rack['x],
the second time with return-state @rack[5] and tape-symbol @rack['y].
It is possible to code the Turing-machine without additional registers,
but this would require a separate coding of the subroutine
for each time it is called with different arguments.
It also would complicate coding the shift of cells to the right.
@rack['B] is the blank, @rack['S] the space and @rack['_] the dummy.
The subroutine uses a mark @rack['M] indicating to which cell it must move
the tape-head before returning. This mark must not occur in the input.

@interaction[
(define registers
 '(#:state          (code:comment "Primary state.")
   #:current-symbol (code:comment "Current tape-symbol.")
   #:prev-symbol    (code:comment "Used for shifting cells to the right.")
   #:return-state   (code:comment "Two arguments for subroutine.")
   #:symbol-arg))
(code:comment " ")
(define rules
 '((code:comment "Check that the input does not contain mark M.")
   ((0 M) (F _ B B B) N)
   ((0 B) (1 S B B B) L)
   ((0 _) (0 _ B B B) R)
   (code:comment "Input ok, rewind the tape.")
   ((1 _) (1 _ B B B) L)
   ((1 B) (2 S B B B) R)
   (code:comment "Call subroutine sub0 with arguments return-state 3 and symbol x.")
   ((2 _) (sub0 _ B 3 x) N)
   (code:comment "After return call the subroutine once more,")
   (code:comment "this time with return-state 5 and symbol y.")
   ((3 _) (4 _ B B B) R)
   ((4 _) (sub0 _ B 5 y) N)
   (code:comment "Upon return, halt.")
   ((5 _) (T _ B B B) N)
   (code:comment "The subroutine.")
   (code:comment "First mark the current cell and")
   (code:comment "memorize the original content (#:current-symbol)")
   (code:comment "in register #:prev-symbol.")
   ((sub0 _) (sub1 M #:current-symbol _ _) R)
   (code:comment "Shift all cells at the right one cell to the right.")
   ((sub1 _) (sub1 #:prev-symbol #:current-symbol _ _) R)
   ((sub1 B) (sub2 #:prev-symbol B _ _) L)
   (code:comment "After reaching the end of the tape, return to the mark.")
   (code:comment "When the mark is found, write the symbol")
   (code:comment "and return from the subroutine.")
   ((sub2 _) (sub2 _ _ _ _) L)
   ((sub2 M) (#:return-state #:symbol-arg B B B) N)))
(code:comment " ")
(define TM
 (make-TM
  0      (code:comment "Initial state.")
  '(T F) (code:comment "Final states.")
  'B     (code:comment "blank")
  'S     (code:comment "space")
  '_     (code:comment "dummy")
  rules
  #:registers registers
  #:name 'TM-with-subroutine))
(code:comment " ")
(TM '())
(code:comment " ")
(TM '(a b c d))]

@subsection{Tower of Hanoi}

The following Turing-machine solves the puzzle of the
@hyperlink["https://en.wikipedia.org/wiki/Tower_of_Hanoi" "Tower of Hanoi"].
It produces the shortest path of moving a tower from one of three pegs to another one.
It expects as input

@inset{@ttt{tower} ‹from› ‹onto› ‹thrd› @rack[1] ...@smaller{@superscript{+}}}

where the number of ones is the height of the tower, id est, the number of disks.
‹from› is the starting peg, ‹onto› the peg of destination and ‹thrd› the third peg.
The pegs must be called @ttt{A}, @ttt{B} and @ttt{C}
in arbitrary order.
The machine checks the correctness of the input.
It replaces a correct input by a sequence of moves:

@inset{[@ttt{disk} ‹from› ‹onto› ‹thrd› @rack[1] ...@smaller{@superscript{+}}]
...@smaller{@superscript{+}}}

where the number of ones indicates which disk is moved
and ‹from›, ‹onto› and ‹thrd› are
the peg the disk is taken from, the peg it is put onto and the third peg.
The smallest disk is indicated by one @rack[1].
Each larger disk by one more @rack[1].
The largest disk is marked by as many ones as the height of the tower being moved.
When a tower-instruction is found, it is replaced by a disk-instruction
and when there are two or more disks,
a tower-instruction with one disk less
is inserted both at the left and at the right
using the same method of inserting one tape-symbol at a time as in section @secref["Subroutine"].
The machine keeps looking for new tower-instructions
and halts when there are no more of them.
The following @seclink["Additional registers" "registers"] are used:

@tabular[#:sep (hspace 1)
(list
 (list " " " " "Required registers.")
 (list @rack[#:state]  ":" "The primary state.")
 (list @rack[#:bus]    ":" "The input/output-register.")
 (list " " " " " ")
 (list " " " " "Additional registers.")
 (list @rack[#:from]   ":" "Starting peg.")
 (list @rack[#:onto]   ":" "Destination peg.")
 (list @rack[#:thrd]   ":" "Third peg.")
 (list " " " " " ")
 (list " " " " (list "Registers for subroutines " @ttt{insertL} " and " @ttt{insertR} "."))
 (list @rack[#:prev]   ":" "Previous tape-symbol during insertion.")
 (list @rack[#:arg]    ":" "Tape-symbol to be inserted.")
 (list @rack[#:return] ":" "Primary state to be assumed after insertion."))]

@interaction0[
(require "make-TM.rkt" racket)

(define registers '(#:state #:bus #:prev #:return #:arg  #:from #:onto #:thrd))

(define rules
'((code:comment "First check the input.")

  ((start  tower) (start1  _     _      _        _      _      _      _    ) R)
  ((start  _    ) (wrong   _     _      _        _      _      _      _    ) N)
  (code:comment "Check the three pegs to be A, B and C in arbitrary order.")
  ((start1 A    ) (A       _     _      _        _      _      _      _    ) R)
  ((start1 B    ) (B       _     _      _        _      _      _      _    ) R)
  ((start1 C    ) (C       _     _      _        _      _      _      _    ) R)
  ((start1 _    ) (wrong   _     _      _        _      _      _      _    ) N)
  ((A      B    ) (AB      _     _      _        _      _      _      _    ) R)
  ((A      C    ) (AC      _     _      _        _      _      _      _    ) R)
  ((A      _    ) (wrong   _     _      _        _      _      _      _    ) N)
  ((B      A    ) (BA      _     _      _        _      _      _      _    ) R)
  ((B      C    ) (BC      _     _      _        _      _      _      _    ) R)
  ((B      _    ) (wrong   _     _      _        _      _      _      _    ) N)
  ((C      A    ) (CA      _     _      _        _      _      _      _    ) R)
  ((C      B    ) (CB      _     _      _        _      _      _      _    ) R)
  ((C      _    ) (wrong   _     _      _        _      _      _      _    ) N)
  ((AB     C    ) (start2  _     _      _        _      _      _      _    ) R)
  ((AB     _    ) (wrong   _     _      _        _      _      _      _    ) N)
  ((AC     B    ) (start2  _     _      _        _      _      _      _    ) R)
  ((AC     _    ) (wrong   _     _      _        _      _      _      _    ) N)
  ((BA     C    ) (start2  _     _      _        _      _      _      _    ) R)
  ((BA     _    ) (wrong   _     _      _        _      _      _      _    ) N)
  ((BC     A    ) (start2  _     _      _        _      _      _      _    ) R)
  ((BC     _    ) (wrong   _     _      _        _      _      _      _    ) N)
  ((CA     B    ) (start2  _     _      _        _      _      _      _    ) R)
  ((CA     _    ) (wrong   _     _      _        _      _      _      _    ) N)
  ((CB     A    ) (start2  _     _      _        _      _      _      _    ) R)
  ((CB     _    ) (wrong   _     _      _        _      _      _      _    ) N)
  (code:comment "At least one 1 required.")
  ((start2 1    ) (start3  _     _      _        _      _      _      _    ) R)
  ((start2 _    ) (wrong   _     _      _        _      _      _      _    ) N)
  ((start3 1    ) (start3  _     _      _        _      _      _      _    ) R)
  ((start3 blank) (rewind  _     _      _        _      _      _      _    ) L)
  ((start3 _    ) (wrong   _     _      _        _      _      _      _    ) N)
  
  (code:comment "Rewind the tape and switch to state 'hanoi'.")

  ((rewind blank) (hanoi    _     _      _       _      _      _      _    ) R)
  ((rewind space) (hanoi    _     _      _       _      _      _      _    ) R)
  ((rewind _    ) (rewind   _     _      _       _      _      _      _    ) L)

  (code:comment "In state 'hanoi' the TM looks for a tower instruction.")
  (code:comment "If a tower instruction is found,")
  (code:comment "immediately make it a disk instruction and,")
  (code:comment "when the tower has more than one disk,")
  (code:comment "insert a tower instruction with one disk less")
  (code:comment "both immediately at the left and at the right")
  (code:comment "of the new disk instruction.")
  (code:comment "If there are no more tower-instructions,")
  (code:comment "the TM halts in succesful state 'halt'.")
  
  ((hanoi   tower) (from    disk  _      _        _      _      _      _    ) R)
  ((hanoi   blank) (halt    _     _      _        _      _      _      _    ) N)
  ((hanoi   space) (halt    _     _      _        _      _      _      _    ) N)
  ((hanoi   _    ) (hanoi   _     _      _        _      _      _      _    ) R)

  (code:comment "Extract the three pegs of the tower instruction.")
  (code:comment "Put them in registers #:from, #:onto and #:thrd.")

  ((from    _    ) (onto    _     _      _        _      #:bus  _      _    ) R)
  ((onto    _    ) (thrd    _     _      _        _      _      #:bus  _    ) R)
  ((thrd    _    ) (right1  _     _      _        _      _      _      #:bus) R)

  (code:comment "Insert a tower instruction at the right.")
  (code:comment "Copy the height, but with one 1 less.")
  (code:comment "m1 is a marked 1, the one being copied.")
  (code:comment "Dont copy the first 1.")
  
  ((right1  1    ) (right2  _     _      _        _      _      _      _    ) R)
  ((right2  1    ) (right3  m1    _      _        _      _      _      _    ) R)
  (code:comment "If there is one disk only in the original tower-instruction,")
  (code:comment "do not insert tower-instructions at the left nor at the right.")
  ((right2  _    ) (rewind  _     _      _        _      _      _      _    ) L)
  (code:comment "Insert a tower instruction at the right.")
  (code:comment "First go to the right of the new disk-instruction.")
  ((right3  1    ) (_       _     _      _        _      _      _      _    ) R)
  (code:comment "Insert 'tower and three pegs.")
  ((right3  _    ) (insertR _     _      right4   tower  _      _      _    ) N)
  ((right4  _    ) (insertR _     _      right5   #:thrd _      _      _    ) N)
  ((right5  _    ) (insertR _     _      right6   #:onto _      _      _    ) N)
  ((right6  _    ) (insertR _     _      right7   #:from _      _      _    ) N)
  (code:comment "Insert a 1.")
  ((right7  _    ) (insertL _     _      right8   1      _      _      _    ) N)
  (code:comment "Go back to marked 1.")
  ((right8  m1   ) (right9  1     _      _        _      _      _      _    ) R)
  ((right8  _    ) (_       _     _      _        _      _      _      _    ) L)
  (code:comment "Marked 1 found.")
  (code:comment "When no more 1s to be copied,")
  (code:comment "go insert tower-instruction at the left.")
  ((right9  tower) (left    _     _      _        _      _      _      _    ) R)
  (code:comment "Next 1 to be copied. mark it.")
  ((right9   1   ) (right10 m1    _      _        _      _      _      _    ) R)
  ((right10  1   ) (right10 _     _      _        _      _      _      _    ) R)
  (code:comment "Go to the tower-instruction being inserted.")
  (code:comment "skip to the right of the three pegs.")
  ((right10 tower) (right11  _     _      _       _      _      _      _    ) R)
  ((right11 _    ) (right12  _     _      _       _      _      _      _    ) R)
  ((right12 _    ) (right13  _     _      _       _      _      _      _    ) R)
  ((right13 _    ) (right14  _     _      _       _      _      _      _    ) R)
  (code:comment "We are at the right of the three pegs.")
  (code:comment "Insert a 1 and go back to the marked 1.")
  ((right14 _    ) (insertL  _     _      right15 1      _      _      _    ) N)
  ((right15 m1   ) (right16  1     _      _       _      _      _      _    ) R)
  ((right15 _    ) (right15  _     _      _       _      _      _      _    ) L)
  (code:comment "Copy next 1.")
  ((right16 1    ) (right10  m1    _      _       _      _      _      _    ) R)
  (code:comment "No more 1s to be copied,")
  (code:comment "go inserting tower instruction at the left.")
  ((right16 _    ) (left     _     _      _       _      _      _      _    ) L)

  (code:comment "Insert a tower instruction at the left.")
  (code:comment "Copy the height, but with one 1 less.")
  (code:comment "m1 is a marked 1, the one being copied.")

  ((left    _    ) (_        _     _      _       _      _      _      _    ) L)
  ((left    disk ) (left1    _     _      _       _      _      _      _    ) N)
  ((left1   _    ) (insertL  _     _      left2   #:onto _      _      _    ) N)
  ((left2   _    ) (insertL  _     _      left3   #:thrd _      _      _    ) N)
  ((left3   _    ) (insertL  _     _      left4   #:from _      _      _    ) N)
  ((left4   _    ) (insertL  _     _      left5   tower  _      _      _    ) N)
  ((left5   _    ) (left5    _     _      _       _      _      _      _    ) R)
  (code:comment "Don't copy the first 1.")
  ((left5   1    ) (left6    _     _      _       _      _      _      _    ) R)
  ((left6   1    ) (left7    m1    _      _       _      _      _      _    ) L)
  (code:comment "No more 1s to be copied.")
  ((left6   _    ) (rewind   _     _      _       _      _      _      _    ) L)
  (code:comment "Go left to the point where to insert the 1.")
  ((left7   _    ) (left7    _     _      _       _      _      _      _    ) L)
  ((left7   disk ) (left8    _     _      _       _      _      _      _    ) N)
  (code:comment "Insert the 1.")
  ((left8   disk ) (insertL  _     _      left9   1      _      _      _    ) N)
  (code:comment "Go back to the marked 1.")
  ((left9   m1   ) (left10   1     _      _       _      _      _      _    ) R)
  ((left9   _    ) (_        _     _      _       _      _      _      _    ) R)
  (code:comment "Copy more 1s, if any left, else rewind and restart.")
  ((left10  1    ) (left11   m1    _      _       _      _      _      _    ) L)
  ((left10  _    ) (rewind   _     _      _       _      _      _      _    ) L)
  ((left11  disk ) (insertL  _     _      left9   1      _      _      _    ) N)
  ((left11  _    ) (_        _     _      _       _      _      _      _    ) L)

  (code:comment "Subroutine for insertion of tape-symbol in register #:arg")
  (code:comment "at the right of the current tape-symbol.")
  (code:comment "Return in state #:return with")
  (code:comment "the tape-head at the inserted tape-symbol.")
  (code:comment "Tape-symbol 'insertL or 'insertR is used to identify the cell")
  (code:comment "where to return to and to insert the tape-symbol.")
  (code:comment "Obviously tape-symbols 'insertL and 'insertR")
  (code:comment "must not be used in any other way.")
  (code:comment "insertR does the same as insertL, but returns with the")
  (code:comment "tape-head at the cell at the right of the inserted cell.")

  ((insertL _      ) (insert1  insertL #:bus _    _      _      _      _    ) R)
  ((insert1 _      ) (insert1  #:prev  #:bus _    _      _      _      _    ) R)
  ((insert1 blank  ) (insert2  #:prev  _     _    _      _      _      _    ) L)
  ((insert1 space  ) (insert2  #:prev  _     _    _      _      _      _    ) L)
  ((insert2 _      ) (insert2  _       _     _    _      _      _      _    ) L)
  ((insert2 insertL) (#:return #:arg   _     _    _      _      _      _    ) N)
  ((insert2 insertR) (#:return #:arg   _     _    _      _      _      _    ) R)
  ((insertR _      ) (insert1  insertR #:bus _    _      _      _      _    ) R)))
(code:comment " ")
(define TM-hanoi
 (make-TM
  'start        (code:comment "initial state")
  '(halt wrong) (code:comment "final states")
  'blank
  'space
  '_            (code:comment "dummy")
  rules
  #:registers registers
  #:name 'TM-hanoi))
(code:comment " ")
(code:comment "Result for 5 disks:")
(code:comment " ")
(define-values (nr-of-moves state tape)
 (TM-hanoi '(tower A B C 1 1 1 1 1)))
(unless (eq? state 'halt)
 (error 'TM-hanoi "incorrect final state: ~s" state))
(let loop ((tape tape) (move-nr 1))
 (cond
  ((null? tape) (newline))
  ((eq? (car tape) 'disk)
   (printf "~n~a : disk "
    (~s #:min-width 2 #:align 'right move-nr))
   (loop (cdr tape) (add1 move-nr)))
  (else
   (printf "~s " (car tape))
   (loop (cdr tape) move-nr))))
(code:comment " ")
(code:comment "Let's test TM-hanoi.")
(code:comment " ")
(define (test height)
 (printf " ~n")
 (define pegs (shuffle '(A B C)))
 (define ones (make-list height 1))
 (define-values (nr-of-TM-moves state tape)
  (TM-hanoi (append (cons 'tower pegs) ones)))
 (code:comment "Simple procedure computing the expected results.")
 (define (compute-expected height f t r)
  (if (zero? height) '()
   (append
    (compute-expected (sub1 height) f r t)
    (append (list 'disk f t r) (make-list height 1))
    (compute-expected (sub1 height) r t f))))
 (code:comment "Compare tape returned by TM-hanoi with expected tape.")
 (define expected-tape (apply compute-expected height pegs))
 (unless (equal? tape expected-tape)
  (error 'TM-hanoi "Wrong results for ~s disks." height))
 (code:comment "Show some results.")
 (define (disk? x) (eq? x 'disk))
 (define nr-of-hanoi-moves (count disk? tape))
 (define (pad n) (~s #:width 6 #:align 'right n))
 (printf "nr of disks: ~a~nnr of moves: ~a~nnr TM moves: ~a~n"
  (pad height) (pad nr-of-hanoi-moves) (pad nr-of-TM-moves))
 #t)
(code:comment " ")
(code:comment "Test heights 1 up to and including 8 disks.")
(code:comment " ")
(when (for/and ((height (in-range 1 9))) (test height))
 (printf " ~nAll is well.~n"))]

For a tower of h disks the number of times a disk is to be moved is 2@superscript{h}@ttt{-}1.
The number of moves of the Turing-machine grows much faster.
Many moves are required for insertion of tower-instructions.
Subroutine @ttt{insert} handles one tape-symbol at a time only.
Hence the machine frequently must move along possibly large parts of the tape,
first forward to the end of the current tape-content and subsequently
back to the cell being inserted.

@section[#:tag "UTM"]{Universal Turing-machine}
The following universal Turing-machine is an adapted copy from
@nonbreaking{"Formal Languages and their Relation to Automata"}
Addison-Wesley, 1969, @nonbreaking{p 105-107} @nonbreaking{(ISBN 0-201-0298 3-9)}
as @elemref["Hopcroft&Ullman" "mentioned above"].
Below the single track tape equivalent of the copied universal Turing-machine is used.
In addition the copy is adapted such as to allow
the encoded Turing-machine to move left of its data.
The universal Turing-machine erases the encoded program before halting,
thus returning the resulting data only.

A universal Turing-machine wants an encoded Turing-machine plus data for its input.
The encoded Turing-machine is enclosed between two triplets @ttt{[c c c]},
the terminating triplet being followed by the data, which, can contain
tape-symbols @rack[0], @rack[1] and the blank @rack['B] only,
but with the current tape-symbol of the data marked as
@rack['m0], @rack['m1] or @rack['mS],
the latter being a marked blank.
The rules are sorted by old state and within an old state by current tape-symbol.
The states are separated by a doublet @ttt{[c c]} and the rules within a state by a single @ttt{c}.
An encoded rule has the form @ttt{[1 ...+ move bit]}, where the number of @rack[1]s in
@ttt{[1 ...+]} identifies the next state.
@ttt{move} is either @rack['R] or @rack['L] and
@ttt{bit} is the symbol to be written,
either @rack[0] or @rack[1].
An omitted rule is included as a @rack[0].
A state with omitted rules @rack[0] only is interpreted as a final state.

The universal Turing-machine accepts symbols
@rack['B] ,@rack['S], @rack[1], @rack['c], @rack['R], @rack['R], @rack['S], @rack['B]
plus the marked version of each symbol obtained by prefixing it with an @ttt{m}.
@rack['B] is the blank and @rack['S] the space.
Marking a blank produces a marked space: @rack['mS].
All rules treat @rack['B] and @rack['S] identically.
The marker is used to identify the rule of the encoded Turing-machine
currently being applied and the current position of its tape-head within the data.
The marker is used too when looking for the encoded rules of the new state
while applying a rule of the encoded Turing-machine.
Hence the marker can have three different meanings,
but it always is clear which one it has.

@Interaction[
(code:comment "Consider:")
(code:comment " ")
(define TM
 (make-TM 1 '(Y) 'B 'S '_
 '(((1 1) (2 0) R)
   ((2 B) (3 1) L) ((2 0) (3 1) L) ((2 1) (2 1) R)
   ((3 B) (Y 0) R) ((3 0) (Y 0) R) ((3 1) (3 1) L))))
(code:comment " ")
(code:comment "Given input (1 1 1) the TM returns (0 1 1 1).")
(code:comment "The following is an encoding of the above TM.")
(code:comment " ")
(define input
(code:comment "The encoded TM.")
'(            c c mc
(code:comment "State 1.")
  0           c    (code:comment "No rule for state 1 with input B.")
  0           c    (code:comment "No rule for state 1 with input 0.")
      1 1 R 0 c c  (code:comment "((1 1) (2 0) R)")
(code:comment "State 2.")
    1 1 1 L 1 c    (code:comment "((2 B) (3 1) L)")
    1 1 1 L 1 c    (code:comment "((2 0) (3 1) L)")
      1 1 R 1 c c  (code:comment "((2 1) (2 1) R")
(code:comment "State 3.")
  1 1 1 1 R 0 c    (code:comment "((3 B) (Y 0) R)")
  1 1 1 1 R 0 c    (code:comment "((3 0) (Y 0) R)")
    1 1 1 L 1 c c  (code:comment "((3 1) (3 1) L)")
(code:comment "State 4: the final state.")
  0           c
  0           c
  0           c c c
(code:comment "The data.")
  m1 1 1))
(code:comment " ")
(code:comment "The universal TM.")
(code:comment " ")
(define UTM-rules-table
(code:comment "The tape-symbols, the second line showing marked symbols.")
'((     0         1         c         L        R        S         B
        m0        m1        mc        mL       mR       mS)
(code:comment "The first column of the table below are old states.")
(code:comment "The abbreviated rules have one of the following forms:")
(code:comment "R = (old-state current-tape-symbol R)")
(code:comment "L = (old-state current-tape-symbol L)")
(code:comment "(new-state move) = (new-state current-tape-symbol move).")
(code:comment "(new-state new-tape-symbol move) = obvious.")
(code:comment "----- indicates the absence of a rule.")
(code:comment "")
(code:comment "First find the current element of the data.")
  (A   (R         R         R         R        R        -----     -----
        -----     -----     (B R)     -----    -----    -----))
  (B   (R         R         R         R        R        -----     -----
        (C0 L)    (C1 L)    -----     -----    -----    (CB L)))
(code:comment "Find the block of the current state.")
  (CB  (L         L         L         L        L        -----     -----
        -----     -----     (DB c R)  -----    -----    -----))
  (C0  (L         L         L         L        L        -----     -----
        -----     -----     (D0 c R)  -----    -----    -----))
  (C1  (L         L         L         L        L        -----     -----
        -----     -----     (D1 c R)  -----    -----    -----))
(code:comment "Find the sub-block corresponding to the current datum.")
(code:comment "Jump to state V when there is no rule for the current datum.")
  (DB  ((V L)     (E m1 L)  -----     -----    -----    -----     -----
        -----     -----     -----     -----    -----    -----))
  (D0  (R         R         (DB R)    R        R        -----     -----
        -----     -----     -----     -----    -----    -----))
  (D1  (R         R         (D0 R)    R        R        -----     -----
        -----     -----     -----     -----    -----    -----))
(code:comment "Rewind to begin of program and mark first block.")
(code:comment "Id est find the first 3 c-s and mark the third one.")
(code:comment "This is marker m2.")
(code:comment "Let m1 be the marker of the current sub-block.")
(code:comment "The distinction between m1 and m2 has been copied from")
(code:comment "Formal Languages and their Relation to Automata, Hopcroft and Ullman.")
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
(code:comment "Locate next state.")
  (J   (R         R         R         R        R        -----     -----
        -----     (KL 1 R)  -----     -----    -----    -----))
(code:comment "For each remaining 1 of next state shift marker m2 to next block")
(code:comment "and shift marker m1 one to the right until no 1-s remain.")
(code:comment "When done go to the block marked with m2")
(code:comment "find the instruction corresponding to the current tape-symbol")
(code:comment "and execute the instruction (TR0, TR1, TL0, or TL1)")
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
(code:comment "Record symbol to be written.")
  (TL  ((TL0 R)   (TL1 R)   -----     -----    -----    -----     -----
        -----     -----     -----     -----    -----    -----))
  (TR  ((TR0 R)   (TR1 R)   -----     -----    -----    -----     -----
        -----     -----     -----     -----    -----    -----))
(code:comment "Find marker in data region and write the new symbol.")
(code:comment "Mark the symbol moved to.")
  (TL0 (R         R         R         R        R        -----     -----
        (U 0 L)   (U 0 L)   R         -----    -----    (U 0 L)))
  (TL1 (R         R         R         R        R        -----     -----
        (U 1 L)   (U 1 L)   R         -----    -----    (U 1 L)))
  (TR0 (R         R         R         R        R        -----     -----
        (U 0 R)   (U 0 R)   R         -----    -----    (U 0 R)))
  (TR1 (R         R         R         R        R        -----     -----
        (U 1 R)   (U 1 R)   R         -----    -----    (U 1 R)))
(code:comment "Adjust the marker and process the new datum.")
(code:comment "Allow move left of the data via state Uc.")
  (U   ((C0 m0 L) (C1 m1 L) (Uc R)    -----    -----    (CB mS L) (CB mS L)
        -----     -----     -----     -----    -----    -----))
(code:comment "We have a move left of the data.")
(code:comment "Insert symbol mS and shift the data one cell to the right.")
(code:comment "After shifting go left to the inserted mS and return to state CB.")
  (Uc  ((U0 mS R) (U1 mS R) -----     -----    -----    -----     -----
        -----     -----     -----     -----    -----    -----))
  (U0  ((U0 R)    (U1 0 R)  -----     -----    -----    (UB 0 L)  (UB 0 L)
        -----     -----     -----     -----    -----    -----))
  (U1  ((U0 1 R)  (U1 R)    -----     -----    -----    (UB 1 L)  (UB 1 L)
        -----     -----     -----     -----    -----    -----))
  (UB  (L         L         -----     -----    -----    -----     -----
        -----     -----     -----     -----    -----    (CB L)))
(code:comment "No new rule found (zero encountered in state DB)")
(code:comment "Check that we have a final state.")
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
(code:comment "We have a final state. Erase all at the left of the data.")
  (ZR  (R         R         R         R        R        (ZL L)    (ZL L)
        R         R         R         R        R        (ZL S L)))
  (ZL  (L         L         (ZS S L)  -----    -----    -----     -----
        (ZL 0 L)  (ZL 1 L)  (ZS S L)  -----    -----    -----))
  (ZS  ((ZS S L)  (ZS S L)  (ZS S L)  (ZS S L) (ZS S L) (Y L)     (Y L)
        (ZS S L)  (ZS S L)  (ZS S L)  (ZS S L) (ZS S L) (Y S L)))))
(code:comment "Y is the final state of the UTM.")
(code:comment " ")
(code:comment "We have to expand UTM-rules-table to a list of rules.")
(code:comment " ")
(define symbols (car UTM-rules-table))
(code:comment " ")
(code:comment "We omit all rules marked as -----.")
(code:comment "The UTM produced by make-TM halts with an error")
(code:comment "when it cannot find an applying rule.")
(code:comment "This may mean that the encoded TM cannot handle its input")
(code:comment "or that the UTM has a bug.")
(code:comment " ")
(define UTM-rules
 (for/fold ((r '()))
  ((rule (in-list (cdr UTM-rules-table))))
  (define old-state (car rule))
  (define UTM-rules
   (for/list
    ((rule (in-list (cadr rule)))
     (old-symbol (in-list symbols))
     #:unless (equal? rule '-----))
    (case rule
     ((R L) (list (list old-state old-symbol) (list old-state old-symbol) rule))
     (else
      (define-values (new-state new-symbol move) 
       (cond
        ((= (length rule) 2) (values (car rule) old-symbol (cadr rule))) 
        (else (apply values rule))))
      (list (list old-state old-symbol) (list new-state new-symbol) move)))))
  (append r UTM-rules)))
(code:comment " ")
(code:comment "The rules of the UTM. None of the rules has a dummy.")
(code:comment " ")
(define width
 (for/fold ((w 0)) ((rule (in-list UTM-rules)))
  (max w (string-length (~s rule)))))
(for ((rule (in-list UTM-rules)) (newline? (in-cycle '(#f #f #f #t))))
 (printf
  (if newline? "~a~n" "~a ")
  (~s #:min-width width #:width width rule)))
(code:comment " ")
(define UTM
 (make-TM
  'A '(Y) 'B 'S '_ UTM-rules #:name 'UTM))
(code:comment " ")
(code:comment "Now let's check that (UTM input)")
(code:comment "produces the same as (TM '(1 1 1)).")
(UTM input)
(code:comment " ")
(TM '(1 1 1))
(code:comment " ")
(code:comment "Encoding of 3 state busy beaver.")
(code:comment "Does move left of the data.")
(code:comment " ")
(define encoded-BB3+data
'(c c mc (code:comment "State 1.")
           1 1 1 R 1 c (code:comment "((1 B) (3 1) R)")
           1 1 1 R 1 c (code:comment "((1 0) (3 1) R)")
               1 R 1 c (code:comment "((1 1) (1 1) R)")
       c (code:comment "State 2.")
               1 R 1 c (code:comment "((2 B) (1 1) R)")
               1 R 1 c (code:comment "((2 0) (1 1) R)")
           1 1 1 L 1 c (code:comment "((2 1) (3 1) L)")
       c (code:comment "State 3.")
             1 1 L 1 c (code:comment "((3 B) (2 1) L)")
             1 1 L 1 c (code:comment "((3 0) (2 1) L)")
         1 1 1 1 R 1 c (code:comment "((3 1) (4 1) R)")
       c (code:comment "State 4, final state.")
                   0 c
                   0 c
                   0 c
       c
       (code:comment "The data, empty but marked as the current tape-symbol:")
       c mS))
(code:comment " ")
(UTM encoded-BB3+data)
(code:comment " ")
(define encoded-BB4+data
'(c c mc       1 1 R 1 c
               1 1 R 1 c
               1 1 L 1 c c
                 1 L 1 c
                 1 L 1 c
             1 1 1 L 0 c c
         1 1 1 1 1 R 1 c
         1 1 1 1 1 R 1 c
           1 1 1 1 L 1 c c
           1 1 1 1 R 1 c
           1 1 1 1 R 1 c
                 1 R 0 c c
             0 c 0 c 0 c c c mS))
(code:comment " ")
(UTM encoded-BB4+data #:report #f)]

The @rack[UTM] requires many moves,
but the final state and tape-content are correct!
If you want a report of the moves of the @rack[UTM],
run module @hyperlink["UTM-with-report.rkt" "UTM-with-report.rkt"],
but be aware that the output has almost 4450 lines
with widths up to 160 characters.
On my simple PC, using DrRacket, it takes about a minute, display of the output included.
@hyperlink["UTM-with-report.rkt" "UTM-with-report.rkt"]
runs the three UTM calls of the above interaction with reports of the first two.

@larger{@larger{@bold{The end}}}
