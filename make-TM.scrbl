#lang scribble/manual

@(require
  scribble/core
  scribble/eval
  racket/match
  racket
  scribble/html-properties
  "make-TM.rkt"
  (for-label "make-TM.rkt"
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
@(define (ttt x) (nonbreaking (element 'tt x)))
@title[#:version ""]{Turing-machines}
@author{Jacob J. A. Koot}
@(defmodule "make-TM.rkt" #:packages ())
This module exports one binding only, that of procedure @rack[make-TM].

@section{Introduction}

Procedure @rack[make-TM] returns a procedure that emulates a two-way single tape
@hyperlink["https://en.wikipedia.org/wiki/Turing_machine" "Turing-machine"]
programmed as described by the arguments given to @rack[make-TM].
The reader is supposed to be familiar with Turing-machines.
Nevertheless a short introduction with the details of the machines as returned by
procedure @rack[make-TM].

@elemtag["book" ""]
@note{John E. Hopcroft and Jeffrey D. Ullman provide a comprehensive description
of Turing-machines in chapter 6 of their book:
@nonbreaking{“Formal Languages and their Relation to Automata”},
@nonbreaking{Addison-Wesley} 1969 @nonbreaking{(ISBN 0-201-0298 3-9)}.}

@elemtag["figure" ""]
@inset[@image["make-TM.jpg"]]

A Turing-machine consists of a control-unit, a tape, a tape-head
and a bidirectional data-bus between the control-unit and the tape-head.
At every moment the control-unit has one out of a finite set of internal states.
The tape has a finite number of cells,
but can stepwise grow in both directions without limitation.
Each cell contains one of a finite set of tape-symbols.
Together the cells form the current tape-content.
The data-bus transports one tape-symbol at a time.
@elemtag["configuration"]{
The configuration of a Turing-machine is its state as a whole including
the internal state of the control-unit,
the current content of the tape and
the current position of the tape-head.}
The first cell of the tape-content is considered to be at the left,
the last one to be at the right.
In the @elemref["figure" "figure"] they are blue.
The current cell (red) is the one below the tape-head and
contains the current tape-symbol.

The Turing-machine must be given an input for the initial tape-content.
The input must be a finite list of non-blank tape-symbols.
The blank is a special tape-symbol used to indicate that a cell is empty
(see @elemref["item 3" "item 3 below"]).
The machine starts with a given initial internal state for the control-unit
and with the tape-head positioned at the leftmost cell of the initial tape-content.
If the input is not empty, the initial tape-content has no blank cell.
If the input is empty, the initial tape-content consists of one single blank cell.
The control-unit makes moves according to a program consisting of a finite set of
instructions, which we call `rules'.
The rule to be applied is determined by the the current internal state of the control-unit
and the current tape-symbol.
The machine halts as soon as the control-unit assumes a final state.
If there is no matching rule, the machine halts in a stuck state.
If it never reaches a final state and never gets stuck, it runs forever,
possibly, but not necessarily, with an ever growing tape-content.
A move consists of three steps:

@inset{@itemlist[#:style 'ordered
          
@item{Optionally putting the control-unit in another internal state.}

@item{Optionally writing a new non-blank tape-symbol in the current cell.
This step is not optional when the current cell is blank.
A blank cell always is filled with a non-blank tape-symbol,
possibly but not necessarily with a space,
which is not a blank.}

@item{@elemtag["item 3"]{Optionally moving the tape-head one cell to the right or to the left.
When the tape-head moves left of the start of the tape-content or right of the end,
a blank cell is added. This cell becomes the current one.
In this way a tape is simulated with an infinite number of
blank cells both at the left and at the right of the actual content.
The new blank cell will be filled with a non-blank tape-symbol during the next move.}}]}

@note{In real life tape-equipment usually the tape is moving
with the tape-head in fixed position.
Moving the tape-head, as assumed for Turing-machines, has the same effect
as keeping it at fixed position and moving the tape in opposit direction.}

@note{The tape-head of a Turing-machine does not move while reading
from a cell or writing into a cell.
Only after it has done its reading from and its writing into the current cell,
the tape-head is moved one cell to the right
or to the left or remains where it is as indicated by the rule being applied.}

@note{Magnetic tape-equipment of the old days (nineteen-sixties, -seventies, -eighties
and even the nineteen-ninetees)
usually destroyed all data following the newly written data,
although with some effort part of it could be recovered.
This equipment was not designed for replacement of part of the data in the middle of a file.
The tape-unit of a Turing-machine does not have this problem,
although it can replace one tape-symbol only at a time.}

Let's start with a simple example of a Turing-machine.
Its states are the initial state @rack['A], the intermediate states @rack['B], @rack['C] and
@rack['D] and the final state @rack['T].
In the rules @rack['R] indicates a move of the tape-head one cell to the right.
In this example the two other options @rack['N] (no move) and @rack['L] (move left)
are not used.
@rack['_] is a dummy, which is not a tape-symbol.
In this example a rule has the form:

@inset{@verbatim[
"((old-state old-tape-symbol)
 (new-state new-tape-symbol)
 move)

old-state       = state
new-state       = state
old-tape-symbol = tape-symbol | dummy
new-tape-symbol = tape-symbol | dummy"]}

A rule applies when its @rack[old-state]
equals the current state of the control-unit
and the @rack[old-tape-symbol] equals the current tape-symbol read from the tape,
or when it is the dummy, which matches every arbitrary tape-symbol.
A rule whose @racket[new-tape-symbol] is a tape-symbol indicates that the content
of the current cell must be replaced by this tape-symbol.
A rule whose @racket[new-tape-symbol] is the dummy indicates that
the current cell must not be altered, unless it is blank,
in which case it is filled with a space, but this does not occur in the present example.
The machine replaces the fourth element by @rack['new].

@interaction[
(require racket "make-TM.rkt")
(code:line)
(define TM
 (make-TM #:name 'first-example
  'A      (code:comment "The initial state.")
  '(T)    (code:comment "The final states, in this case one only.")
  'blank  (code:comment "Not used.")
  'space  (code:comment "Not used.")
  '_      (code:comment "The dummy.")
  (code:comment "The rules:")
  '((code:comment "Do not modify first  tape-symbol.    Move right.")
    ((A _) (B _  ) R)    
    (code:comment "Do not modify second tape-symbol.    Move right.")
    ((B _) (C _  ) R)    
    (code:comment "Do not modify third  tape-symbol.    Move right.")
    ((C _) (D _  ) R)    
    (code:comment "Replace fourth tape-symbol by 'new'. Move right and halt.")
    ((D _) (T new) R))))
(code:line)
(TM '(This is the original tape))]

The returned values are the number of moves made, the final state and
the modified content of the tape.
Let's see more details in a report of the moves.
In such a report the new content of the tape is shown as
@tt{((tape-symbol ...) (current tape-symbol ...))} representing the content
@tt{(tape-symbol ... current tape-symbol...)} where @tt{current} is the current tape-symbol.
With the given input,
the following machine replaces the second and the fifth tape-symbol.

@interaction[
(require racket "make-TM.rkt")
(code:line)
(define TM
 (make-TM #:name 'second-example
  'A      (code:comment "The initial state.")
  '(T)    (code:comment "The final state.")
  'blank  (code:comment "Not used.")
  'space  (code:comment "Not used.")
  '_      (code:comment "The dummy.")
  '(((A          _) (A _        ) R)
    ((A        did) (A will     ) R)
    ((A yesterday?) (T tomorrow?) N))))
(code:line)
(TM '(What did you do yesterday?) #:report 'long)]

@section{Additional registers}
The control unit of a Turing-machine emulated by a procedure made by @rack[make-TM]
has at least two registers.
The first one is the primary state-register and the second one the input/output-register,
but the control-unit may have more registers.
During a move new values can be put into the registers, possibly obtained from other registers.
A Turing-machine with more than two registers
is equivalent to a Turing-machine with only two registers
as long as the combined contents of the registers is limited to a finite set.
Allowing more registers is a way to simplify the description of the rules.
For example, multiple registers make it easier to describe rules that move part of the content
of the tape to another position on the tape.
They also help the simulation of subroutines. See section @secref{Subroutines}.
It always is possible, although it may be tedious, to rewrite rules with more than 2 registers
as a set of rules with 2 registers by including the contents of the additional registers in the
primary state. For an example, compare section @secref["Inserting symbols"] with
section @secref["More registers"].

@section{Procedure make-TM}
@defform-remove-empty-lines[@defform[#:kind "procedure"
(make-TM initial-state final-states
          blank space dummy
          rules
          [#:registers registers #:name name])
#:grammar(
(initial-state state)
(final-states  (final-state ...))
(blank         tape-symbol)
(space         tape-symbol)
(rules         (rule ...))
(registers     (code:line @#,element["roman"]{default =} 2)
               (code:line (register-name register-name register-name ...))
               nr-of-registers)
(name          (code:line @#,(element "roman" "default =") @#,(racket 'TM-without-name))
               symbol)
(final-state   state)
(rule          (selector updater move))
(selector      (old-state old-symbol))
(updater       (new-state new-symbol register ...))
(old-state     state)
(new-state     state dummy register-name)
(old-symbol    tape-symbol dummy)
(new-symbol    tape-symbol dummy register-name)
(register      new-state new-symbol))
#:contracts
((          state (not/c (or/c dummy keyword?)))
 (    tape-symbol (not/c (or/c dummy keyword?)))
 (          dummy (not/c keyword?))
 (  register-name keyword?)
 (nr-of-registers (and/c exact-integer? (>=/c 2)))
 (           move (or/c 'R 'L 'N))
 (         symbol symbol?)
)]{
Procedure @rack[make-TM] returns a procedure that emulates a Turing-machine.
Keywords are reserved for the names of registers.
Providing an @racketlink[exact-integer? "exact integer"] @tt{n≥2}
for @rack[registers] is the same as providing:

@inset{@rack[(for/list ((k (in-range n))) (string->keyword (~s k)))]}

For example, @nonbreaking{@rack[#:registers]@(hspace 1)@rack[3]}
does the same as @nonbreaking{@rack[#:registers]@(hspace 1)@rack['(#:0 #:1 #:2)]}.
The first @rack[register-name] is for the primary state-register and the second one
for the input/output-register.
Before the machine is produced the arguments are checked to satisfy all contracts
and the following conditions,
equality or being distinct to be understood in the sense of @rack[equal?].

@inset{@itemlist[#:style 'ordered
 @item{The @rack[space], the @rack[blank] and the @rack[dummy] must be distinct.}
 @item{The list of @rack[final-states] must not contain duplicates}
 @item{The list of @rack[final-states] must not contain any @rack[old-state].}
 @item{The @rack[rules] must have distinct @rack[selector]s.}
 @item{Every @rack[updater] must have as many elements as there are @rack[registers].}
 @item{Every keyword in a @rack[rule] must be one of the @rack[register-name]s.}
 @item{The list of @rack[register-name]s must not contain duplicates.}]}

When not all of these conditions are satisfied,
procedure @rack[make-TM] raises an @rack[error].

The @rack[name] is attached to the returned procedure.
It is used when printing a report and in error-messages.

@section{Running a Turing-machine}
The control-unit interprets the @rack[rules] as follows,
equality again to be understood in the sense of @rack[equal?].
The first @rack[register] will be referred to as the primary state-register
and its content as the primary state.
The second @rack[register] is the input/output-register.
It contains the @rack[tape-symbol] read from or to be written into
the current cell under the tape-head.

@inset{@itemlist[#:style 'ordered
@item{A Turing-machine halts if the primary state equals one of the @rack[final-states],
      else it continues with the following steps.}

@item{The current tape-symbol is read and put into the input/output-register.@(linebreak)
      The tape-head does not move during this reading.}

@item{A rule is looked for.
A @rack[rule] applies if its @rack[old-state] equals the current primary state
and the @rack[old-symbol] matches the current tape-symbol in the input/output-register.
The @rack[dummy] matches every tape-symbol.
Every other @rack[old-symbol] matches only when equal to the current tape-symbol.
A @rack[rule] whose @rack[old-symbol] equals the current tape-symbol
prevails over a @rack[rule] with the same @rack[old-state] and
whose @rack[old-symbol] is the @rack[dummy].
For @rack[rules] with the same @rack[old-state] the @rack[dummy]
is like @rack[else] in a @rack[cond]- or @rack[case]-form,
but is not required to be at the end.
The order of the @rack[rules] is irrelevant.
When there is no matching rule the machine halts in a stuck state by raising an @rack[error].}

@item{The @rack[registers] are updated.
The element with index k of the @rack[updater]
of the rule indicates what to put in register k.
Let x be element k of the @rack[updater].

∘ If x is a @rack[dummy] register k remains unaffected.@(linebreak)
∘ If x is a @rack[register-name] the old content of that register is put into register k.
@(linebreak)
∘ If x is a @rack[state] or a @rack[tape-symbol], it is put into register k.

For example, assuming there are three registers with the names @rack[#:state], @rack[#:symbol]
and @rack[#:extra],
then the @rack[updater] @rack[(new-state #:extra #:symbol)] indicates that
register @rack[#:state] is filled with @rack[new-state] and the registers @rack[#:symbol]
and @rack[#:extra] exchange their content.
@rack[new-state] will be the new primary state and
the old content of register @rack[#:extra], which becomes the new content of register
@rack[#:symbol] will be written into the current cell of the tape as described in the next item.}

@item{Now the @rack[tape-symbol] of the input/output-register is written in the current cell
of the tape, replacing the former current tape-symbol.
However, if the input/output-register contains a @rack[blank] a @rack[space] is written.
During this operation the tape-head does not move.}

@item{Finally the tape-head may be moved:@(linebreak)
@rack[move] @rack['L] : move the tape-head one cell to the left.@(linebreak)
@rack[move] @rack['R] : move the tape-head one cell to the right.@(linebreak)
@rack[move] @rack['N] : don't move the tape-head.@(linebreak)
When the tape-head moves to the left of the left-most cell of the tape or to the right of
the right-most cell,
a blank cell is added and the tape-head is positioned at this cell.
These are the only two situations in which a @rack[blank] is written.}

@item{The above process is repeated until the primary state equals a @rack[final-state]
      or the machine gets stuck because it has no rule for the current primary state
      and the current tape-symbol.}]}

A procedure returned by procedure @rack[make-TM],
say @(bold (element 'tt (bold "Turing-machine"))),
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
The @rack[output] is the final content of the tape but without heading or trailing
@rack[blank] or @rack[space]s.
It can contain @rack[space]s, but not at the begin nor at the end.

@note{One can imagine the tape to have an infinite number of blank cells both at the left
and at the right of its current non-blank content.
In that case moving left or right of the current content does not require writing a blank
because it already is there.
A nicer name for a blank cell would be `empty cell',
but in @elemref["book" "the book mentioned above"] the word `blank' is used.}

@note{In the formal definition of a Turing-machine there is a finite set of @rack[tape-symbol]s.
The machines returned by procedure @rack[make-TM] may,
but do not necessarily limit the input to a predefined set of @rack[tape-symbol]s.
They can use the union of the set of
@rack[tape-symbol]s in the @rack[input] and those
that can be extracted from the arguments given to procedure @rack[make-TM].
This means that formally, procedure @rack[make-TM]
does not return a completely defined Turing-machine.
The definition is completed by the @rack[input] at the moment
the procedure that emulates the machine is called.
At that moment we have a running procedure that emulates
a Turing-machine with a finite set of @rack[tape-symbol]s
in accordance with the formal definition.}

@note{Define a @italic{regular} rule as a rule without @rack[dummy]s.
The @rack[dummy] allows a finite multitude of @italic{regular} rules to be written
as one single rule.
When the set of @rack[tape-symbol]s allowed in the initial content of the tape is known,
every @rack[rule] containing one or more @rack[dummy]s
can be written as a finite collection of regular @rack[rule]s.
Hence, using @rack[dummy]s is not an offence against the formal definition of Turing-machines.}

@note{No distinction is made between registers that can contain a @rack[state]
      and those that can contain a @rack[tape-symbol].
      In fact no distinction is made between @rack[state]s and @rack[tape-symbol]s.
      For example the rule @rack[((A B) (B A) N)] indicates that
      @rack[state] @rack[A] becomes @rack[state] @rack[B] and that
      the current @rack[tape-symbol] @rack[B] is replaced by @rack[tape-symbol] @rack[A].
      Here @rack[A] and @rack[B] are used both for a @rack[state] and for a @rack[tape-symbol].
      This is not in contradiction with the formal definition of Turing-machines.
      The set of @rack[tape-symbol]s and the set of @rack[state]s
      are not required to be disjunct.
      The rules can always be rewritten such as to make the two sets disjunct.}

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
      the original content of the input/output-register already showing the current tape-symbol.}
@item{The new position of the tape-head and the new content of the tape shown as
@nonbreaking{@tt{((h ...) (c t ...))}},
where the new position of the tape-head is at tape-symbol @tt{c}.}]}

@note{Internally list @rack[(h ...)] is guarded in reversed order,
which allows fast movement of the tape-head.
This is like using a push-down/pop-up machine with two stacks.
Indeed, every Turing-machine can be simulated by such a machine.
When the content of the tape is to be shown, the stack containing the head is reversed
such as to show the cells in correct order.}

If @rack[report] is @rack['short] the Turing-machine
prints a short record of the moves it makes (on the @racket[current-output-port])
For each move the report shows the move-counter
the old and new primary state and the new content of the tape.

If @rack[report] is @rack[#f], which is the default value, no report is written.

When @rack[limit] is an @racketlink[exact-positive-integer? "exact positive integer"]
the Turing-machine halts by raising an error
when no @rack[final-state] is encountered within @rack[limit] moves.
When @rack[limit] is @rack[#f] and the Turing-machine never reaches a @rack[final-state],
the procedure keeps running forever,
unless it halts with an error because it cannot find an applying rule.
                                                 
@section{Halting problem}
Many Turing-machines never halt.
Sometimes this can be predicted by looking at the @rack[rules] only,
sometimes by inspection of both the @rack[rules] and the @rack[input].
However, because of the
@hyperlink["https://en.wikipedia.org/wiki/Halting_problem"]{Halting Problem}
there always remain cases for which it is impossible to decide whether or not the machine will halt.
Procedure @rack[make-TM] and the Turing-machines it produces
do no checks at all against infinite loops.
Whether or not a Turing-machine halts may depend on its input.
Argument @rack[limit] provides protection.
The following trivial Turing-machine
obviously would loop forever with arbitrary input when it would not be halted by
the @rack[limit]:

@interaction[
(require racket "make-TM.rkt")
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
While the @rack[TM] is running,
its @elemref["configuration" "configuration"] never changes after the first move,
which could be detected while the @rack[TM] is running.
However, the @rack[TM] does no such check.
As another example consider:

@interaction[
(require racket "make-TM.rkt")
(define TM (make-TM
            'A     (code:comment "initial state")
            '()    (code:comment "no final state")
            'B     (code:comment "blank")
            'S     (code:comment "space")
            '_     (code:comment "dummy")
            '(((A _) (B 1) R)
              ((B _) (A 0) R))
            #:name 'Another-non-halting-TM))
(code:line)
(TM '() #:report 'short #:limit 10)]

It is obvious that the above machine, no matter its initial tape-content, never halts,
although it never reproduces the same @elemref["configuration" "configuration"].

@note{Procedure @rack[make-TM] could be adapted such as to
predict the infinite loops of the last two examples just by checking the rules.
It also could be adapted such as to produce
Turing-machines that can detect a repeated @elemref["configuration" "configuration"].
These adaptations have not been made,
for the Halting Problem implies that there always remain cases
in which it is not possible to predict whether or not the machine will halt.}}}]

@section{Examples}

Some of the examples are inspired by material of Jay McCarthy
that can be found in @hyperlink["http://jeapostrophe.github.io/2013-10-29-tmadd-post.html"
                                "http://jeapostrophe.github.io/2013-10-29-tmadd-post.html"].

In the examples @rack['B] usually is a blank, @rack['S] a space and @rack['_] the dummy.
Usually @rack['T] is the final state for an accepted input and @rack['F] for a rejected input.

@subsection{Blank → space}

When a rule instructs to write a blank, in fact a space is written:

@interaction[
(require "make-TM.rkt")
(define TM
 (make-TM 'A '(T) 'blank 'space 'dummy
 '(((A blank) (B x) R)
   ((B blank) (C blank) R) (code:comment "A space is written.")
   ((C blank) (T y) R))
  #:name 'TM:blank->space))
(TM '() #:report 'long)]

@subsection{Subroutines}
Every Turing-machine whose tape can be extended at both ends
can be simulated by a Turing-machine that never extends its tape at the left.
The machine below starts in state @rack[a].
The program includes a subroutine that starts with state @rack[sub0]
and wants two arguments, the state to return to and a tape-symbol to be inserted.
These arguments are put in registers @rack[#:return-state] and @rack[#:symbol-arg].
The subroutine shifts all at the right of the current cell one cell to the right,
moves back to the cell it came from,
writes the given @rack[#:symbol-arg]
and returns by entering the @rack[#:return-state].
The subroutine is called twice.
The first time with return-state @rack[b] and tape-symbol @rack[x],
the second time with return-state @rack[d] and tape-symbol @rack[y].
It is possible to code the machine without additional registers,
but this would require a separate coding of the subroutine
for each time it is called.
It also would complicate coding the shifting of cells of the tape one place to the right.

@interaction[
(require "make-TM.rkt")
(code:line)
(define registers
 '(#:state
   #:current-symbol
   #:prev-symbol
   #:return-state
   #:symbol-arg)) 
(code:line)
(define rules
 (code:comment "Make sure the mark cannot be confused with symbol mark in the input.")
 (code:comment "The mark is used to mark the cell where to return to")
 (code:comment "after all cells have been shifted one place to the right.")
 (let ((mark (string->uninterned-symbol "‹mark›")))
  (code:comment "Notice the quasiquotation '`'. It is used to insert the mark as ',mark'")
 `((code:comment "Call subroutine sub0 with arguments return-state b and symbol x.")
   ((a _) (sub0 _ _ b x) N)
   (code:comment "After return call the subroutine once more,")
   (code:comment "this time with return-state d and symbol y.")
   ((b _) (c _ B B B) R)
   ((c _) (sub0 _ _ d y) N)
   (code:comment "Upon return, halt.")
   ((d _) (T _ _ _ _) N)
   (code:comment "The subroutine.")
   (code:comment "First mark the current cell and")
   (code:comment "memorize the original content in #:prev-symbol.")
   ((sub0 _) (sub1 ,mark #:current-symbol _ _) R)
   (code:comment "Shift all cells at the right one cell to the right.")
   ((sub1 _) (sub1 #:prev-symbol #:current-symbol _ _) R)
   ((sub1 B) (sub2 #:prev-symbol B _ _) L)
   (code:comment "After reaching the end of the tape, return to the mark.")
   (code:comment "When the mark is found, write the symbol")
   (code:comment "and return from the subroutine.")
   ((sub2 _) (sub2 _ _ _ _) L)
   ((sub2 ,mark) (#:return-state #:symbol-arg B B B) N))))
(code:line)
(define TM
 (make-TM
  'a   (code:comment "Initial state.")
  '(T) (code:comment "Final state.")
  'B
  'S
  '_
  rules
  #:registers registers))
(code:line)
(TM '() #:report #t)
(code:line)
(TM '(a) #:report #t)
(code:line)
(TM '(mark mark mark) #:report #t)
(code:line)
(TM '(a b c d) #:report #t)]

@subsection{List-ref}
The following machine expects as input @rack[(1 ... / tape-symbol ...+)]
Let k be the number of ones before the slash.
The machine halts in state @rack[T] after replacing all non-spaces by spaces,
the one with index k in the list @rack[(tape-symbol ...+)] excepted.
Spaces in this list do not count for the index.
If there are less than k+1 non-spaces,
the machine halts in state @rack[F] with empty tape,
id est consisting of spaces only.

@interaction[
(require racket "make-TM.rkt")
(code:line)
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
  ((E S) (A S) R) (code:comment "We are at the start of the tape. Repeat.")
  ((G S) (G S) R) (code:comment "Keep looking for first non-space.")
  ((G _) (H _) R) (code:comment "Found the non-space.")
  ((G B) (I S) N) (code:comment "Error, no non-space found")
  ((H _) (H S) R) (code:comment "Erase all following the non-space.")
  ((H B) (T S) N) (code:comment "Done.")
  ((I B) (J S) R) (code:comment "Error case.")
  ((I _) (I S) L) (code:comment "Erase the whole tape and")
  ((J B) (F S) N) (code:comment "halt in final state F.")
  ((J _) (J S) R)))
(code:line)
(define TM
 (make-TM
  'A     (code:comment "Initial state.")
  '(T F) (code:comment "Final states.")
  'B     (code:comment "Blank")
  'S     (code:comment "Space")
  '_     (code:comment "Dummy")
  rules
  #:name 'list-ref-TM))
(code:line)
(TM '(1 1 1 / a b c d e f) #:report 'short)
(code:line)
(define input '(a S b S c S d S e S f S g S h S i S j S k))
(code:line)
(for ((k (in-range 0 15)))
 (define-values (nr-of-moves state tape)
  (TM (append (make-list k 1) '(/) input)))
 (printf "k=~s, nr-of-moves=~s, final-state=~s, tape=~s~n"
  k nr-of-moves state tape))]

@subsection{Remove symbols}
The following Turing-machine always halts.
A correct input is a list of which every element is an @tt["*"] or a @tt["+"],
The result of a correct input is the input without @tt["+"]
followed by n+1 spaces if there are n plus-signs.
This is like addition of zero, one or more natural numbers,
where natural number k is written as `@tt["* ..."]' with k @tt["*"]s.
The machine never moves left of the start of the input.

@interaction[
(require racket "make-TM.rkt")
(code:line)
(define rules
'((code:comment "State 0 : Inspect the very first cell.")
  (code:comment "          Mark start * with x or start + with p.")
  (code:comment "          This way we can detect the start of the input")
  (code:comment "          when moving left and avoid moving left")
  (code:comment "          of the start of the input.")
  ((0 *) (1 x) R)  (code:comment "Ok, go check the remainder of the input.")
  ((0 +) (1 p) R)  (code:comment "Ok, go check the remainder of the input.")
  ((0 B) (T S) N)  (code:comment "Empty input accepted.")
  ((0 _) (F _) N)  (code:comment "Reject incorrect input.")
  (code:comment "State 1 : Check the remainder of the input.")
  ((1 *) (1 *) R)  (code:comment "Ok, continue the check.")
  ((1 +) (1 +) R)  (code:comment "Ok, continue the check.")
  ((1 B) (2 S) L)  (code:comment "Input is ok. Start the addition.")
  ((1 _) (F _) N)  (code:comment "Reject incorrect input.")
  (code:comment "State 2 : Do the addition from right to left.")
  (code:comment "          When entering state 2 the tape-head is at")
  (code:comment "          the right-most cell that is not a space.")
  ((2 *) (2 *) L)  (code:comment "Leave * as it is and continue addition.")
  ((2 x) (T *) N)  (code:comment "Start of input reached. Done.")
  ((2 +) (3 *) R)  (code:comment "Replace + by * and go replacing the last * by a space.")
  ((2 p) (T S) R)  (code:comment "Replace p by a space and we are ready.")
  (code:comment "State 3 : Go to end of tape.")
  ((3 *) (3 *) R)  (code:comment "Keep looking for end of input.")
  ((3 S) (4 S) L)  (code:comment "End of input reached.")
  (code:comment "State 4 : Replace the last * by a space and continue addition.")
  (code:comment "          The current tape-symbol is guaranteed to be an *.")
  ((4 *) (2 S) L)))
(code:line)
(define TM (make-TM #:name 'remove-plus-signs
            '0     (code:comment "initial state")
            '(T F) (code:comment "final states")
            'B     (code:comment "blank")
            'S     (code:comment "space")
            '_     (code:comment "dummy")
            rules))
(code:line)
(TM '(* + * * + * * *) #:report 'short)
(code:line)
(code:comment "Let's test this machine:")
(code:line)
(random-seed 0)
(for/and ((n* (in-range 0 10)))
 (define expected (make-list n* '*))
 (for/and ((n+ (in-range 0 10)))
  (define input (append expected (make-list n+ '+)))
  (for/and ((k (in-range 0 20)))
   (define-values (nr-of-moves final-state output) (TM (shuffle input)))
   (and (eq? final-state 'T) (equal? output expected)))))
(code:line (TM '() #:report 'long) (code:comment "What happens with empty input?"))
(code:line (TM '(+ + +) #:report 'short) (code:comment "What happens with plusses only?"))]

@subsection{Binary addition}
The following Turing-machine adds two natural numbers written in binary notation.
The machine halts with every arbitrary input.
A correct input is defined as follows:

@inset{@verbatim[
"input   = (operand + operand)
operand = bit ...+
bit     = 0 | 1"]}

An incorrect input yields @itel{final-state} @element['tt "F"].
A correct input yields @itel{final-state} @element['tt "T"] and @tt{output}
@nonbreaking{@rack[(bit bit ...)]}
showing the sum of the two operands.
More precisely the @tt{output} is @nonbreaking{@rack[(1 bit ...)]} or @rack[(0)],
id est, without leading zeros.
The initial content of the tape is modified such as to result in the sum.
In the sum a 0 bit is written as @element['tt "o"] and a 1 bit as @element['tt "y"]
such as to know which bits already have been established and which ones yet have to be computed.
During the addition the content of the tape is (ignoring spaces and blank) 
@nonbreaking{@element['tt "(0-or-1 ... x-or-y ... + 0-or-1 ...)"]}.
Bits of the second operand are processed starting from the least significant one.
Every such bit is replaced by a @itel["space"] before it is processed.
The significance of this bit is the same as that of
the right-most bit @nonbreaking{@element['tt "0-or-1"]} of the first operand.
After all bits of the second operand have been processed,
the @element['tt "+"] is removed,
tape-symbols @element['tt "x"] and @element['tt "y"] are reverted to
@element['tt "0"] and @element['tt "1"] and leading zeros are removed.

@interaction[
(require racket "make-TM.rkt")
(code:line)
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
(code:line)
(define adder (make-TM #:name 'binary-addition
               '0     (code:comment "initial state")
               '(T F) (code:comment "final states")
               'B     (code:comment "blank")
               'S     (code:comment "space")
               '_     (code:comment "dummy")
               rules))
(code:line)
(adder '(1 0 1 1 + 1 0 1 1 1) #:report 'short)
(code:line)
(adder '(0 0 0 1 1 + 0 0 1 1))
(code:line)
(adder '(0 0 0 + 0 0) #:report 'short)
(code:line)
(code:comment "Testing the Turing-machine.")
(code:comment "We need two procedures for conversion between")
(code:comment "exact nonnegative integer numbers and lists of bits.")
(code:line)
(code:comment "Procedure exact-nonnegative-integer->list-of-bits converts")
(code:comment "exact nonnegative integer n to a list of bits 0 and 1.")
(code:line)
(define (exact-nonnegative-integer->list-of-bits n)
 (if (zero? n) '(0)
  (let loop ((n n) (r '()))
   (cond
    ((zero? n) r)
    ((even? n) (loop (quotient n 2) (cons 0 r)))
    (else      (loop (quotient n 2) (cons 1 r)))))))
(code:line)
(code:comment "Procedure list-of-bits->exact-nonnegative-integer converts")
(code:comment "a list of bits 0 and 1 to an exact nonnegative integer")
(code:line)
(define (list-of-bits->exact-nonnegative-integer lst)
 (let loop ((r 0) (lst (reverse lst)) (e 1))
  (cond
   ((null? lst) r)
   ((= (car lst) 0) (loop r (cdr lst) (* 2 e)))
   ((= (car lst) 1) (loop (+ r e) (cdr lst) (* 2 e))))))
(code:line)
(code:comment "Check that list-of-bits->exact-nonnegative-integer is")
(code:comment "the inverse of exact-nonnegative-integer->list-of-bits.")
(code:line)
(random-seed 0)
(for*/and ((m (in-range 0 100)))
 (define n (if (< m 50) m (random 30000000)))
 (= n
  (list-of-bits->exact-nonnegative-integer
   (exact-nonnegative-integer->list-of-bits n))))
(code:line)
(code:comment "Test the Turing-machine.")
(code:line)
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
The following machine expects @nonbreaking{@element['tt "((n m) ...)"]} as input,
where each @element['tt "n"] and each @element['tt "m"] is a decimal digit coded as
an exact integer between 0 (inclusive) and 10 (exclusive).
The machine adds the numbers @element['tt "n..."] and @element['tt "m..."] and returns the sum
@element['tt "s..."]
The machine passes first to the end of the input.
Subsequently it does the adddition in one pass to the left
going from the least to the most significant digit.
Redundant heading zeros are not removed.
It replaces each @itel{tape-symbol} @nonbreaking{@element['tt "(n m)"]} by one decimal digit.
State @element['tt "0"] indicates that there is no carry.
State @element['tt "1"] indicates that a carry must be added.
State @element['tt "A"] is the initial internal state and @element['tt "T"] the final state.

@interaction[
(require racket "make-TM.rkt")
(code:line)
(define rules
 (append
  (list
   '((A _) (A _) R) (code:comment "First go to the right.")
   '((A B) (0 S) L)
   '((0 B) (T S) L) (code:comment "All done.")
   '((1 B) (T 1) L))
  (for*/list
   ((c (in-range 0 2))  (code:comment "0 = no carry, 1 = carry")
    (n (in-range 0 10)) (code:comment "digit of first operand")
    (m (in-range 0 10)) (code:comment "digit of second operand"))
   (define-values (q r) (quotient/remainder (+ n m c) 10))
   `((,c (,n ,m)) (,q ,r) L))))
(code:line)
(begin
 (printf "The rules~n")
 (pretty-print (take rules 30))
 (printf "etc.~n")
 (pretty-print (take (drop rules (- (quotient (length rules) 2) 15)) 30))
 (printf "etc.~n")
 (pretty-print (drop rules (- (length rules) 30))))
(code:line)
(define TM (make-TM #:name 'decimal-addition
            'A   (code:comment "initial state")
            '(T) (code:comment "final state")
            'B   (code:comment "blank")
            'S   (code:comment "space")
            '_   (code:comment "dummy")
            rules))
(code:line)
(TM '((9 9) (0 0) (0 0) (9 9) (9 9)))
(code:line)
(code:comment "nr->lst takes an exact nonnegative integer and")
(code:comment "returns its list of digits.")
(code:line)
(define (nr->lst n)
 (define (nr->lst n result)
  (cond
   ((zero? n) result)
   (else
    (define-values (q r) (quotient/remainder n 10))
    (nr->lst q (cons r result)))))
 (if (zero? n) '(0) (nr->lst n '())))
(code:line)
(code:comment "prepare-input takes two exact nonnegative integers")
(code:comment "and returns the corresponding input for TM.")
(code:line)
(define (prepare-input n m)
 (let ((n (nr->lst n)) (m (nr->lst m)))
  (define ln (length n))
  (define lm (length m))
  (define len (max ln lm))
  (map list (append (make-list (- len ln) 0) n)
            (append (make-list (- len lm) 0) m))))
(code:line)
(code:comment "output->nr converts the output of the TM")
(code:comment "to an exact nonnegative integer.")
(code:line)
(define (output->nr lst)
 (define (output->nr lst)
  (if (null? lst) 0
   (+ (car lst) (* 10 (output->nr (cdr lst))))))
 (output->nr (reverse lst)))
(code:line)
(let ((n 9876) (m 987654))
 (define-values (nr-of-moves final-state output)
  (TM (prepare-input n m) #:report 'short))
 (define sum (output->nr output))
 (values sum (= sum (+ n m))))
(code:line)
(code:comment "Test the TM.")
(code:line)
(for/and ((k (in-range 0 1000)))
 (define n (random 1000000000))
 (define m (random 1000000000))
 (define-values (nr-of-moves final-state output) (TM (prepare-input n m)))
 (and (= (output->nr output) (+ n m)) (eq? final-state 'T)))]

@subsection{@hyperlink["https://en.wikipedia.org/wiki/Busy_beaver" "Busy beaver"]}
@subsubsection{3 state @hyperlink["https://en.wikipedia.org/wiki/Busy_beaver" "busy beaver"]}
In fact there are four states, but @itel{final-state} @tt{T} does not count.
The Turing-machine program shown here takes 2 moves less than the one shown in
Wikipedia article @hyperlink["https://en.wikipedia.org/wiki/Busy_beaver" "busy beaver"].
Another interesting point is, that the one shown here never writes a @rack[0].
As in this example @rack[0] is a blank,
it even would be impossible to write a @rack[0].

@note{
Some authors make no distinction between a @italic{@tt{blank}} and a @italic{@tt{space}},
meaning that they allow writing a @italic{@tt{blank}}.
I prefer to make the distinction.}

@interaction[
(require racket "make-TM.rkt")
(define rules
 '(((A 0) (C 1) R)
   ((A 1) (A 1) R)
   ((B 0) (A 1) R)
   ((B 1) (C 1) L)
   ((C 0) (B 1) L)
   ((C 1) (T 1) N)))
(define TM
 (make-TM #:name '3-state-busy-beaver
  'A   (code:comment "The initial state.")
  '(T) (code:comment "The final state.")
  0    (code:comment "The blank.")
  'space-not-used
  'dummy-not-used
  rules))
(TM '() #:report 'long)]

@subsubsection{4 state @hyperlink["https://en.wikipedia.org/wiki/Busy_beaver" "busy beaver"]}
In fact there are five states, but @itel{final-state} @tt{T} does not count.
For every non-final state @rack[X] there are two rules,
@rack[((X _) (? ?) ?)] and
@rack[((X 1) (? ?) ?)].
This implies that a blank @rack['B] and tape-symbol @rack[0] always
are treated in the same way whenever encountered as the current tape-symbol.
This removes the distinction between these two tape-symbols.

@interaction[
(require racket "make-TM.rkt")
(define rules
 '(((A _) (B 1) R)
   ((A 1) (B 1) L)
   ((B _) (A 1) L)
   ((B 1) (C 0) L)
   ((C _) (T 1) R)
   ((C 1) (D 1) L)
   ((D _) (D 1) R)
   ((D 1) (A 0) R)))
(define TM
 (make-TM #:name '4-state-busy-beaver
  'A   (code:comment "The initial state.")
  '(T) (code:comment "The final state.")
  'B   (code:comment "The blank.")
  'space-not-used
  '_
  rules))
(TM '() #:report 'short)]

@subsection["{0,1}"@superscript{*}]

The following Turing-machine halts on every arbitrary input.
If the input is a list of zeros and ones with as many zeros as ones,
the @itel{final-state} is @rack['T].
In all other cases the @itel{final-state} is @rack['F].
The machine accepts an empty input immediately.
If the input is not empty, a starting mark @rack['s] is added at the left,
the input is checked to consist of zeros and ones only
and an ending mark @rack['e] is added at the end of the input.
Now the tape-head is at the cell immediately left of the end-mark @rack['e].
The following process is repeated until halted.
Starting from the right, the machine looks at the left for a @rack[0] or a @rack[1].
If a @rack[0] is encountered, it is replaced by @rack['e] and a required @rack[1] is looked for.
If a @rack[1] is encountered, it is replaced by @rack['e] and a required @rack[0] is looked for.
After finding a required @rack[0] or @rack[1], it is replaced by @rack['S],
the tape-head is positioned at the right of the tape
and the process is repeated until no more ones or zeros are present.
If a required @rack[0] or @rack[1] is not found, the machine halts in state @rack['F].

@interaction[
(require racket "make-TM.rkt")
(code:line)
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
   (code:comment "state 3: Go to the end of the tape.")
   ((3 e) (4 e) L)
   ((3 _) (3 _) R)
   (code:comment "state 4: look for a 0 or a 1 at the left")
   ((4 s) (T e) N) (code:comment "Ok, no more 0s or 1s.")
   ((4 0) (5 e) L) (code:comment "a 1 at the left is required.")
   ((4 1) (6 e) L) (code:comment "a 0 at the left is required.")
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
   ((6 S) (6 S) L)))
(code:line)
(define TM
 (make-TM #:name 'zeros-and-ones
  0      (code:comment"initial state")
  '(T F) (code:comment"final states")
  'B     (code:comment"blank")
  'S     (code:comment"space")
  '_     (code:comment"dummy")
  rules))
(code:line)
(TM '(0 1 0 0 1 1 1 0) #:report 'short)
(code:line)
(code:comment "Let's do some tests.")
(code:line)
(define (test input expected)
 (define-values (n s t) (TM input))
 (or (eq? expected s)
  (error 'test "this is wrong: ~s ~s ~s ~s" input n s t)))
(code:line)
(for*/and ((n0 (in-range 0 10)) (n1 (in-range 0 10)))
 (define input (append (make-list n0 0) (make-list n1 1)))
 (for/and ((n (in-range 0 100)))
  (test (shuffle input) (if (= n0 n1) 'T 'F))))]

@subsection{Matching parentheses}

The following machine reads @rack['<] as a left parenthesis
an @rack['>] as a right parenthesis.
The machine halts in state @rack[T] if the parentheses are well balanced
and no other symbols occur in the @itel{input}.
In all other cases the machine halts in state @rack[F].
The method used in the following example is as follows.
First check that the input consists of @rack['<] and @rack['>] only.
Put @itel{tape-symbol} @rack[s] at the left of the input
and @itel{tape-symbol} @rack[e] at the right.
This helps detecting the start and the end of the current content of the tape.
Starting from the right go left look for a @rack['>]
whose first preceding non-space symbol is @rack['<].
When found replace the @rack['<] and the @rack['>]
by spaces, go to the right of the input and repeat.
When looking for a @rack['>] all symbols appear to be spaces, the machine halts in state @rack[T].
When encountering a @rack['<] before encountering a @rack['>] the parentheses are not balanced
and the machine halts in state @rack[F].
There are @nonbreaking{(2n)!/(n!(n+1)!)} ways to write n pairs of matching parentheses, n≥0.
See @hyperlink["https://en.wikipedia.org/wiki/Catalan_number" "Catalan numbers"].

@interaction[
(require racket "make-TM.rkt")
(code:line)
(define rules
  (code:comment "state 0")
  (code:comment "accept empty input.")
  (code:comment "put start marker s before non-empty input.")
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
(code:line)
(define TM (make-TM 0 '(T F) 'B 'S '_ rules #:name 'parentheses))
(code:line)
(code:comment "match-parentheses does the same as the TM. Used for tests.")
(code:line)
(define (match-parentheses lst)
 (define (match-parentheses lst n)
  (cond
   ((null? lst) (if (zero? n) 'T 'F))
   ((eq? (car lst) '<) (match-parentheses (cdr lst) (add1 n)))
   ((zero? n) 'F)
   (else (match-parentheses (cdr lst) (sub1 n)))))
 (match-parentheses lst 0))
(code:line)
(code:comment "Test now.")
(code:comment "Try all (expt 2 k) inputs of k elements,")
(code:comment "k running from 0 to 10 (inclusive).")
(code:comment "A total of 2047 tests of which only 65 yield final state T.")
(code:line)
(for*/fold ((count 0) (total 0))
 ((k (in-range 0 11)) (n (in-range (arithmetic-shift 1 k))))
 (define input
  (for/list ((k (in-range 0 k)))
   (if (zero? (bitwise-and (arithmetic-shift 1 k) n)) '< '>)))
 (define-values (nr-of-moves state output) (TM input))
 (unless (eq? state (match-parentheses input)) (error 'Test "test failed"))
 (cond
  ((eq? state 'T)
   (printf "~a ~s~n"
    (~s #:min-width 2 #:align 'right (add1 count))
    input)
   (values (add1 count) (add1 total)))
  (else (values count (add1 total)))))]

When counting a @rack['<] as @element['tt "+1"] and an @rack['>] as @element['tt "-1"],
going from left to right the addition must never go below zero and must end in zero.
The following machine uses such a counter.
It is put at the end of the input between two slashes.
The counter consists of @rack[0]s and @rack[1]s,
and the number of @rack[1]s is the count.
When decreasing the counter the first @rack[1] is replaced by a @rack[0].
If no @rack[1] can be found, the parentheses do not match.
When increasing the counter the first @rack[0] is replaced by a @rack[1],
or, if no @rack[0] can be found, a @rack[1] is added at the end.
After all parentheses have been processed,
the counter is checked to be zero.

@interaction[
(require "make-TM.rkt")
(code:line)
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
  (code:comment "Erase the tape.")
  ((B _) (B S) L)
  ((B S) (T S) N)
  ((B B) (T S) N)))
(code:line)
(define TM (make-TM 1 '(F T) 'B 'S '_ rules))
(code:line)
(code:line (TM '(<) #:report 'short) (code:comment "Final state F."))
(code:line)
(code:line (TM '(>) #:report 'short) (code:comment "Final state F."))
(code:line)
(code:line (TM '(> <) #:report 'short) (code:comment "Final state F."))
(code:line)
(code:line (TM '(< < < > < > > >) #:report 'short) (code:comment "Final state T."))
(code:line)
(code:comment "match-parentheses does the same as the TM. Used for tests.")
(code:comment "The same as in the previous example.")
(code:comment "To do: to avoid duplicate code in interactions.") 
(code:line)
(define (match-parentheses lst)
 (define (match-parentheses lst n)
  (cond
   ((null? lst) (if (zero? n) 'T 'F))
   ((eq? (car lst) '<) (match-parentheses (cdr lst) (add1 n)))
   ((zero? n) 'F)
   (else (match-parentheses (cdr lst) (sub1 n)))))
 (match-parentheses lst 0))
(code:line)
(code:comment "Test now.")
(code:comment "Try all (expt 2 k) inputs of k elements,")
(code:comment "k running from 0 to 10 (inclusive).")
(code:comment "A total of 2047 tests of which only 65 yield final state T.")
(code:line)
(for*/fold ((count 0) (total 0))
 ((k (in-range 0 11)) (n (in-range (arithmetic-shift 1 k))))
 (define input
  (for/list ((k (in-range 0 k)))
   (if (zero? (bitwise-and (arithmetic-shift 1 k) n)) '< '>)))
 (define-values (nr-of-moves state output) (TM input #:report #f))
 (unless (eq? state (match-parentheses input)) (error 'Test "test failed"))
 (cond
  ((eq? state 'T) (values (add1 count) (add1 total)))
  (else (values count (add1 total)))))]

@subsection[#:tag "Inserting symbols"]{Inserting symbols}

The following Turing-machine always halts.
For an input consisting of @rack['a]s and @rack['b]s only
the @itel{final-state} is @rack['T] and symbol @rack['x] is inserted
between each @rack['a] and an immediately following @rack['b].
The insertion of @rack['x] requires that the tape-symbols
preceding the @rack['b] are shifted one cell to the left.
An input containing anything other than @rack['a] or @rack['b]
yields @itel{final-state} @rack['F].
@rack[0] is the initial state.

@interaction[
(require racket "make-TM.rkt")
(code:line)
(define rules
'((code:comment "Look for a.")
  ((0  a) (1  a) R)
  ((0  b) (0  b) R)
  ((0  B) (T  S) N)
  ((0  _) (F  _) N)
  (code:comment "Symbol a found, is next symbol b?")
  ((1  a) (1  a) R) (code:comment "Keep looking for b.")
  ((1  b) (2  M) L) (code:comment "yes, mark it M and proceed.")
  ((1  _) (F  _) N)
  ((1  B) (T  S) N)
  (code:comment "Rewind the tape.")
  ((2  B) (3  S) R)
  ((2  _) (2  _) L)
  (code:comment "Shift every symbol one cell to the left up to mark M.")
  (code:comment "Replace a or b or x by S.")
  (code:comment "Replace preceding S by a or b or x.")
  (code:comment "Replace M by b and replace preceding S by x.")
  (code:comment "Memorize the symbol in the new state.")
  ((3  a) (4a S) L)
  ((3  b) (4b S) L)
  ((3  x) (4x S) L)
  ((3  M) (4M b) L)
  ((4a S) (5  a) R) (code:comment "Continue the shift.")
  ((4b S) (5  b) R) (code:comment "Continue the shift.")
  ((4x S) (5  x) R) (code:comment "Continue the shift.")
  ((4M S) (0  x) R) (code:comment "Shift completed. Look for next a followed by b.")
  (code:comment "Step to the right of the S and continue the shift.")
  ((5  S) (3  S) R)))
(code:line)
(define TM (make-TM  0 '(T F) 'B 'S  '_ rules))
(code:line)
(code:comment "Example:")
(code:line)
(TM '(b a b a b a) #:report 'short)
(code:line)
(code:comment "Let's test the TM.")
(code:comment "The following procedure does the same as the TM")
(code:comment "It is used to test the TM.")
(code:line)
(define (ab->axb input)
 (cond
  ((null? input) '())
  ((null? (cdr input)) input)
  ((equal? (take input 2) '(a b))
   (append '(a x b) (ab->axb (cddr input))))
  (else (cons (car input) (ab->axb (cdr input))))))
(code:line)
(random-seed 0) (code:comment "Let's do the tests now:")
(code:line)
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

Represent natural number n as @tt{x ...} or @tt{y ...} with n @tt{x}s or @tt{y}s.
The following Turing-machine never halts when given an empty input.
It forms an infinite tape containing the numbers 0, 1, 2 etc.
separated by slashes.
Every next number is formed by putting an @tt{x} at the end of the content
and copying the previous number, which has the form @tt{x ...}.
While copying, the @tt{x}s of the previous number are replaced by @tt{y}s
such as to indicate they already have been copied.

@interaction[
(require racket "make-TM.rkt") 
(code:line)
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
  ((4 x) (5 y) R) (code:comment "Mark x as copied and go put x at end of tape.")
  ((4 y) (4 y) L) (code:comment "y has already been copied. Keep looking for x.")
  ((4 /) (6 /) R) (code:comment "Copy is complete.")
  ((5 _) (5 _) R) (code:comment "Go to end of tape, write x and")
  ((5 B) (3 x) L) (code:comment "continue copying.")
  (code:comment "Next number complete.")
  ((6 _) (6 _) R) (code:comment "Go to end of tape.")
  ((6 B) (2 /) R) (code:comment "Go form the next nr.")
  ))
(code:line)
(define TM
 (make-TM #:name 'counter
 '0   (code:comment "initial state")
 '()  (code:comment "no final state")
 'B   (code:comment "blank")
 'space-not-used
 '_   (code:comment "dummy")
 rules))
(code:line)
(code:comment "Limit the number of moves.")
(code:comment "The error message shows the resulting content of the tape.")
(TM '() #:limit 162 #:report 'short)]

The following counter is like the previous one,
but writes its numbers in binary notation and every new one at the left of the previous one.
Bits 0 and 1 are used, but the most recently computed number consists of bits o for 0 and i for 1.
Bits o and i indicate that they have not yet been copied.
Every next number is formed by copying the most recent one
while converting o and i of the original to 0 and 1.
i is added to the copy before the next number is generated.

@interaction[
(require "make-TM.rkt")
(define rules
'(
  (code:comment "First form tape (/ o /).")
  ((0  B) (1  /) L) (code:comment "Write /")
  ((1  B) (2  o) L) (code:comment "Write o")
  ((2  B) (3  /) R) (code:comment "Write /")
  (code:comment "Copy the number at the start of the tape.")
  (code:comment "Look for the least significant bit o or i.")
  ((3  /) (4  _) L) (code:comment "Position found.")
  ((3  0) (4  _) L) (code:comment "Position found.")
  ((3  1) (4  _) L) (code:comment "Position found.")
  ((3  o) (3  _) R) (code:comment "Keep looking at the right.")
  ((3  i) (3  _) R) (code:comment "Keep looking at the right")
  (code:comment "Copy the least significant bit just found.")
  ((4  /) (8  _) L) (code:comment "All copied, go add i=1 to the copy.")
  ((4  o) (5o 0) L) (code:comment "Mark as copied and go put bit o at start of tape.")
  ((4  i) (5i 1) L) (code:comment "Mark as copied and go put bit i at start of tape.")
  (code:comment "Go to end of tape and write the bit memorized in state 5o or 5i")
  ((5o _) (5o _) L)
  ((5o B) (6  o) R) (code:comment "write the o.")
  ((5i _) (5i _) L)
  ((5i B) (6  i) R) (code:comment "write the i.")
  (code:comment "Go to the end of the number.")
  ((6  /) (3  _) R) (code:comment "End found. Go look for the next bit to copy.")
  ((6  _) (6  _) R)
  (code:comment "Add o=0, but put / at the start of the tape.")
  ((7  B) (3  /) R) (code:comment "Done, go for the next number.")
  ((7  o) (7  o) L)
  ((7  i) (7  i) L)
  (code:comment "Add i=1.")
  ((8  B) (9  i) L) (code:comment "Done, go write terminating /.")
  ((8  o) (7  i) L)
  ((8  i) (8  o) L)
  (code:comment "Write terminating / and go for the next number.")
  ((9  B) (3  /) R)))
(code:line)
(define TM (make-TM 0 '() 'B 'S '_ rules #:name 'binary-counter))
(TM '() #:limit 175 #:report 'short)]

@subsection[#:tag "More registers"]{More registers}
The Turing-machines shown sofar in this document have one data-register and
one state-register only.
Let us use a Turing-machine with two data-registers to simplify and to speed up
the example of section @secref{Inserting symbols}.
One extra data-register is used.
It memorizes the previously replaced symbol when shifting tape-symbols to the left
in order to make space for an x.

O@interaction[
(require racket "make-TM.rkt")
(code:line)
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
(code:line)
(define TM
 (make-TM  0 '(T F) 'B 'S  '_ rules
  #:registers '(#:state #:current #:previous)))
(code:line)
(TM '(b a b a b a) #:report 'long)
(code:line)
(code:comment "Let's test the TM.")
(code:comment "The following procedure does the same as the TM.")
(code:comment "It is used to test the TM.")
(code:line)
(define (ab->axb input)
 (cond
  ((null? input) '())
  ((null? (cdr input)) input)
  ((equal? (take input 2) '(a b)) (append '(a x b) (ab->axb (cddr input))))
  (else (cons (car input) (ab->axb (cdr input))))))
(code:line)
(random-seed 0)
(code:line)
(for*/and ((na (in-range 20)) (nb (in-range 20)))
 (define ab (append (make-list na 'a) (make-list nb 'b)))
 (for/and ((k (in-range 100)))
  (define input (shuffle ab))
  (define-values (nr-of-moves state output) (TM input))
  (define expect (ab->axb input))
  (and
   (equal? (ab->axb input) output)
   (equal? state 'T))))]

@subsection{Universal Turing-machine}
The following Universal Turing-machine is an adapted copy from
@nonbreaking{"Formal Languages and their Relation to Automata"}
as @elemref["book" "mentioned above"].

@interaction[
(require racket "make-TM.rkt")
(code:line)
(code:comment "Universal Turing Machine")
(code:comment "Copied from “Formal Languages and their Relation to Automata”,")
(code:comment "Addison-Wesley, 1969, p 105-107 (ISBN 0-201-0298 3-9)")
(code:comment "I have replaced the entries in column mc")
(code:comment "and rows TL0, TL1, TR0 and TR1 by an R.")
(code:comment "In the book these are underscores, but that does not work.")
(code:comment "Below the single tape equivalent of the copied UTM is used.")
(code:line)
(code:comment "Consider")
(code:line)
(define TM
 (make-TM 1 '(Y) 'B 'S '_
 '(((1 1) (2 0) R)
   ((2 B) (3 1) L) ((2 0) (3 1) L) ((2 1) (2 1) R)
   ((3 B) (Y 0) R) ((3 0) (Y 0) R) ((3 1) (3 1) L))))
(code:line)
(code:comment "Given input '(1 1 1) the TM returns '(0 1 1 1).")
(code:comment "The following is an encoding of the above TM.")
(code:comment "(1 ... move bit) is a rule, the number of 1s specifies the new state,")
(code:comment "the bit being the 0 or 1 to be written.")
(code:comment "0 indicates absence of a rule.")
(code:comment "Rules are separated by c.")
(code:comment "The rules are in order of the tape-symbols B, 0 and 1.")
(code:comment "States are separated by c c.")
(code:comment "The states are in order 1, 1 1, 1 1 1 and 1 1 1 1")
(code:comment "A rule 0 indicates absence of a rule.")
(code:comment "A final state is marked as one with all rules 0.")
(code:comment "This holds for state 4 (1 1 1 1).")
(code:comment "State 4 corresponds to state Y of the above TM.")
(code:comment "m is used as marker, initially marking the block of state 1.")
(code:comment "m is is also used as marker for the current symbol in the data.")
(code:comment "The marked version of symbol x is mx.")
(code:comment "A symbol x without mark simply is x itself.")
(code:comment "Notice that m is not used as a separate tape-symbol.")
(define input
(code:comment "The encoded Turing machine.")
'(c c mc
(code:comment "The encoded machine accepts the tape-symbols B, 0 and 1.")
(code:comment "For every state there are 3 rules, one for B, one for 0 and one for 1.")
(code:comment "B           0             1")
(code:comment "State 1.")
  0           c 0           c   1 1 R 0
  c c
(code:comment "State 2.")
    1 1 1 L 1 c   1 1 1 L 1 c   1 1 R 1
  c c
(code:comment "State 3.")
  1 1 1 1 R 0 c 1 1 1 1 R 0 c 1 1 1 L 1
  c c
(code:comment "State 4, the final state.")
  0           c 0           c 0
  c c c
(code:comment "The data.")
  m1 1 1))
(code:line)
(code:comment "The universal Turing-machine.")
(code:line)
(define simplified-rules
(code:comment "The tape-symbols:")
'((     0         1         c         L        R        S         B
        m0        m1        mc        mL       mR       mS)
(code:comment "The rules (states in the first column)")
(code:comment "R = (_ _ R), L = (_ _ L)")
(code:comment "stop and error are erroneous final states.")
(code:comment "(new-state move) = (new-state _ move).")
(code:comment "(new-state new-symbol move) obvious.")
(code:comment "")
(code:comment "First find the current element of the data.")
  (A   (R         R         R         R        R        stop      stop
        stop      stop      (B R)     stop     stop     stop))
  (B   (R         R         R         R        R        stop      stop
        (C0 L)    (C1 L)    stop      stop     stop     (CB L)))
(code:comment "Find the block of the current state.")
  (CB  (L         L         L         L        L        stop      stop
        stop      stop      (DB c R)  stop     stop     stop))
  (C0  (L         L         L         L        L        stop      stop
        stop      stop      (D0 c R)  stop     stop     stop))
  (C1  (L         L         L         L        L        stop      stop
        stop      stop      (D1 c R)  stop     stop     stop))
(code:comment "Find the sub-block corresponding to the current datum.")
(code:comment "Jump to state V when there is no rule for the current datum.")
  (DB  ((V L)     (E m1 L)  stop      stop     stop     stop      stop
        error     error     error     error    error    error))
  (D0  (R         R         (DB R)    R        R        stop      stop
        error     error     error     error    error    error))
  (D1  (R         R         (D0 R)    R        R        stop      stop
        error     error     error     error    error    error))
(code:comment "Rewind to start of program and mark first block.")
(code:comment "Id est find the 3 starting c-s and mark the third one.")
(code:comment "This is marker m2.")
(code:comment "Let m1 be the marker of the current sub-block.")
(code:comment "The distinction between m1 and m2 has been copied from")
(code:comment "Formal Languages and their Relation to Automata, Hopcroft and Ullman.")
  (E   (L         L         (F L)     L        L        stop      stop
        error     error     error     error    error    error))
  (F   ((E L)     (E L)     (G L)     (E L)    (E L)    stop      stop
        error     error     error     error    error    error))
  (G   ((E L)     (E L)     (H R)     (E L)    (E L)    stop      stop
        error     error     error     error    error    error))
  (H   (stop      stop      (I R)     stop     stop     stop      stop
        error     error     error     error    error    error))
  (I   (stop      stop      (J mc R)  stop     stop     stop      stop
        error     error     error     error    error    error))
(code:comment "Locate next state.")
  (J   (R         R         R         R        R        stop      stop
        stop      (KL 1 R)  stop      stop     stop     stop))
(code:comment "For each remaining 1 of next state shift marker m2 to next block")
(code:comment "and shift marker m1 one to the right until no 1-s remain.")
(code:comment "When done go to the block marked with m2")
(code:comment "find the instruction corresponding to the current tape-symbol")
(code:comment "and execute the instruction (TR0, TR1, TL0, or TL1)")
  (KL  (stop      (ML m1 L) stop      (TL R)   (TR R)   stop      stop
        error     error     error     error    error    error))
  (ML  (L         L         L         L        L        stop      stop
        stop      stop      (NL c R)  stop     stop     stop))
  (NL  (R         R         (PL R)    R        R        stop      stop
        stop      (NR R)    stop      stop     stop     stop))
  (PL  ((NL R)    (NL R)    (SL mc R) (NL R)   (NL R)   stop      stop
        stop      (NR R)    stop      stop     stop     stop))
  (SL  (R         R         R         R        R        stop      stop
        stop      (KL 1 R)  stop      stop     stop     stop))
  (KR  (stop      (MR m1 R) stop      (TL R)   (TR R)   stop      stop
        error     error     error     error    error    error))
  (MR  (R         R         R         R        R        stop      stop
        stop      stop      (NL c R)  stop     stop     stop))
  (NR  (R         R         (PR R)    R        R        stop      stop
        error     error     error     error    error    error))
  (PR  ((NR R)    (NR R)    (SR mc L) (NR R)   (NR R)   stop      stop
        error     error     error     error    error    error))
  (SR  (L         L         L         L        L        stop      stop
        stop      (KR 1 R)  stop      stop     stop     stop))
(code:comment "Record symbol to be written.")
  (TL  ((TL0 R)   (TL1 R)   stop      stop     stop     stop      stop
        error     error     error     error    error    error))
  (TR  ((TR0 R)   (TR1 R)   stop      stop     stop     stop      stop
        error     error     error     error    error    error))
(code:comment "Find marker in data region and write the new symbol.")
  (TL0 (R         R         R         R        R        stop      stop
        (U 0 L)   (U 0 L)   stop      stop     stop     (U 0 L)))
  (TL1 (R         R         R         R        R        stop      stop
        (U 1 L)   (U 1 L)   R         stop     stop     (U 1 L)))
  (TR0 (R         R         R         R        R        stop      stop
        (U 0 R)   (U 0 R)   R         stop     stop     (U 0 R)))
  (TR1 (R         R         R         R        R        stop      stop
        (U 1 R)   (U 1 R)   R         stop     stop     (U 1 R)))
(code:comment "Adjust the marker and process the new datum.")
  (U   ((C0 m0 L) (C1 m1 L) stop      stop     stop     (CB mS L) (CB mS L)
        error     error     error     error    error    error))
(code:comment "No new rule found (zero encountered in state DB)")
(code:comment "Check that we have a final state.")
  (V   (L         L         (W L)     L        L        stop      stop
        error     error     error     error    error    error))
  (W   ((V L)     (V L)     (X1 R)    (V L)    (V L)    stop      stop
        error     error     error     error    error    error))
  (X1  (stop      stop      (X2 R)    stop     stop     stop      stop
        error     error     error     error    error    error))
  (X2  ((X3 R)    stop      stop      stop     stop     stop      stop
        error     error     error     error    error    error))
  (X3  (stop      stop      (X4 R)    stop     stop     stop      stop
        error     error     error     error    error    error))
  (X4  ((X5 R)    stop      stop      stop     stop     stop      stop
        error     error     error     error    error    error))
  (X5  (stop      stop      (X6 R)    stop     stop     stop      stop
        error     error     error     error    error    error))
  (X6  ((ZR R)    stop      stop      stop     stop     stop      stop
        error     error     error     error    error    error))
(code:comment "We have a final state. Erase all at the left of the data.")
  (ZR  (R         R         R         R        R        (ZL L)    (ZL L)
        R         R         R         R        R        (ZL S L)))
  (ZL  (L         L         (ZS S L)  error    error    error     error
        (ZL 0 L)  (ZL 1 L)  (ZS S L)  error    error    error))
  (ZS  ((ZS S L)  (ZS S L)  (ZS S L)  (ZS S L) (ZS S L) (Y L)     (Y L)
        (ZS S L)  (ZS S L)  (ZS S L)  (ZS S L) (ZS S L) (Y S L)))
  ))
(code:line)
(code:comment "We have to expand the simplified rules.")
(code:line)
(define symbols (car simplified-rules))
(code:line)
(code:comment "We omit all rules with new state error or stop.")
(code:comment "The UTM produced by make-TM halts with an error for these two states.")
(code:line)
(define rules
 (for/fold ((r '()))
  ((rule (in-list (cdr simplified-rules))))
  (define old-state (car rule))
  (define rules
   (for/list
    ((rule (in-list (cadr rule)))
     (old-symbol (in-list symbols))
     #:when (not (or (equal? rule 'stop) (equal? rule 'error))))
    (case rule
     ((R L) (list (list old-state old-symbol) (list old-state old-symbol) rule))
     (else
      (define-values (new-state new-symbol move) 
       (cond
        ((= (length rule) 2) (values (car rule) old-symbol (cadr rule))) 
        (else (apply values rule))))
      (list (list old-state old-symbol) (list new-state new-symbol) move)))))
  (append r rules)))
(code:line)
(code:comment "The rules of the UTM. None of the rules has a dummy.")
(code:line)
(define width
 (for/fold ((w 0)) ((rule (in-list rules)))
  (max w (string-length (~s rule)))))
(for ((rule (in-list rules)) (newline? (in-cycle '(#f #f #f #t))))
 (if newline?
  (printf "~a~n" (~s #:min-width width #:width width rule))
  (printf "~a "  (~s #:min-width width #:width width rule))))
(code:line)
(define UTM
 (make-TM
  'A '(Y) 'B 'S '_ rules #:name 'UTM))
(code:line)
(code:comment "Now let's check that (UTM input)")
(code:comment "produces the same as (TM '(1 1 1)).")
(code:line)
(TM '(1 1 1))
(UTM input)]

The Universal Turing-machine requires many more moves,
but the final state and tape-content are correct!
If you want a report of the moves of the @rack[UTM],
run module @hyperlink["UTM-with-report.rkt" "UTM-with-report.rkt"],
but be aware that the output has almost 2000 lines
with widths of up to 155 characters.
Nevertheless, on my simple PC it runs within 15 seconds, producing the output included.

@larger{@larger{@bold{The end}}}
