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

@title[#:version ""]{Turing machines}
@author{Jacob J. A. Koot}
@(defmodule "make-TM.rkt" #:packages ())

@section{Introduction}
This document describes procedure @rack[make-TM], which
returns procedures that emulate two-way single tape
@hyperlink["https://en.wikipedia.org/wiki/Turing_machine" "Turing Machines"].
The reader is supposed to be familiar with Turing machines.

@note{John E. Hopcroft and Jeffrey D. Ullman give a very accurate description of
Turing machines
in their book @nonbreaking{Formal Languages and their Relation to Automata (ISBN 0-201-0298 3-9)}}

Nevertheless a short introduction in which
confusion between words referring to @hyperlink["http://racket-lang.org/" "Racket"] objects
and those referring to abstract Turing machines is avoided.
For example, the word `tape-symbol' will be used for the symbols of the tape of a Turing machine
in order to avoid confusion with symbols of Racket.

@elemtag["figure" " "] @inset[@image["make-TM.jpg"]]

At every moment the control unit has one out of a finite set of internal states.
The whole state of a Turing machine includes the state of all components of the machine,
id est, the internal state of the control unit,
the current content of the tape and the current position of the read/write-head.
The first element of the tape-content is considered to be at the left,
the last element to be at the right.
In the @elemref["figure" "above figure"] these elements are shown in blue.
The current element (red) is the one currently below the read/write-head.
The elements of the content are tape-symbols,
but the first or last element can be an empty element,
which is not a tape-symbol.
Initially the content consists of a finite input of tape-symbols
and the read/write-head is positioned at the leftmost element.
If the input is empty, the content of the tape initially consists of one empty element.
The tape-content can grow to arbitrary size, but always is finite.
The number of distinct whole states can be infinite,
but always is denumerable. 
The control unit makes moves according to a finite set of rules
until it assumes a final state.
The rule to be applied is determined by the internal state 
of the control unit and the current element.
A move consists of three steps:

@itemlist[#:style 'ordered
@item{Optionally putting the control unit in another internal state.}
@item{Optionally replacing the current tape-symbol by another tape-symbol.
This step is not optional when the current element is empty.
During a move an empty element always is filled with a tape-symbol, possibly with a blank.}
@item{Optionally moving the read/write-head one step to the right or to the left.}]

@note{In real life tape equipment usually the tape is moving
while the read/write-head remains in fixed position.
Moving the read/write-head has the same effect as keeping it in fixed position and moving
the tape in opposit direction.}

The machine never writes a dummy or empty element.
It cannot remove elements from the content of the tape,
but it can replace the current element by a blank,
which is a tape-symbol.
A Turing machine can be programmed such as to shift all elements at the left/right of
the current element to the left/right by one or more elements and to put blanks or other
tape-symbols in the resulting free space.
Empty elements are used only to extend the tape
at the left or at the right of the current content.
When moving the read/write-head at the left of the begin of the content of the tape
or at the right of the end, an empty element is added and
the read/write-head is positioned at this element.
In this way an infinite tape is simulated with an infinite number of
empty elements both at the left and at the right of the actual content.
In fact the content never has more than one empty element.
If it has one, it is the first one or the last one and it is the current element.
It will be filled with a tape-symbol during the next move.
The dummy is for use in rules only.
The rules describe how the control unit makes its moves.
Which rule is to be applied is determined by the current internal state of the control-unit
and the current element of the tape.
The machine repeats moves until a final state is obtained,
or runs forever if it never enters a final state.
It is possible to put a limit on the number of moves
such as to raise an exception when the emulated machine needs more moves.
It may happen that there is no rule corresponding to
the combination of the current internal state and the current element.
If this happens, the procedure that emulates the Turing machine halts by raising an exception.

For the moment assume that the control unit has one register for its internal state
and one input/output-register containing the tape-element read from the tape
or to be written onto the tape.
The internal states and tape-elements can be arbitrary
@hyperlink["http://racket-lang.org/" "Racket"] values other than the dummy and keywords.
Usually symbols and exact integer numbers are the most convenient ones.
Lists or vectors can be used to simulate a multi-tape Turing machine.
Equivalence relation @rack[equal?] is used for comparison of two internal states
or two tape-elements.
The internal states and tape-elements live in separate worlds.
An internal state never is compared to a tape-element.
Hence the Turing machine will not be confused when the intersection of the set of
@hyperlink["http://racket-lang.org/" "Racket"]-objects representing the
internal states and the set of those representing the tape-elements is not empty
or when an internal state equals the empty element.
However, this may confuse a human reader of the rules that describes the control unit.
After reaching a final state the procedure that emulates the Turing machine
returns the number of moves it has made, the final state and its output.
The latter consists of the final content of the tape,
but without heading or trailing empty element or blanks.
The output can contain blanks but not at the start or the end.
The output never contains a dummy or an empty element.
Let's start with a simple example of a Turing machine.
It's states are @rack['A], @rack['B], @rack['C], @rack['D] and @rack['E].
In the rules @rack['R] indicates a move to the right.
@rack['N] indicates that no move must be made and @rack['L] a move to the left,
but the example does not make moves to the left.
@rack['_] is the dummy. A rule has the form

@rack[((old-state current-element) ((new-state) (tape-symbol-to-be-written) move))].

A rule whose @rack[current-element] is the dummy applies to every arbitrary current element
of the tape.
A rule whose @rack[tape-symbol-to-be-written] is the dummy indicates that the current element
must not be altered (except that if it is an empty element, it is filled with a blank)
The machine accepts every input and replaces the fourth element by @rack['new].

@interaction[
(require racket "make-TM.rkt")
(code:line)
(define TM
 (make-TM
  'A      (code:comment "The initial state.")
  '(E)    (code:comment "The final state.")
  'empty
  'blank
  '_      (code:comment "The dummy.")
  (code:comment "The rules:")
  '(((A _) ((B) (_  ) R)) (code:comment "Do not modify first  tape-element.    Move right.")
    ((B _) ((C) (_  ) R)) (code:comment "Do not modify second tape-element.    Move right.")
    ((C _) ((D) (_  ) R)) (code:comment "Do not modify third  tape-element.    Move right.")
    ((D _) ((E) (new) N)) (code:comment "Replace fourth tape-element by 'new'. Don't move.")
    )))
(code:line)
(TM '(This is the original tape))]

The returned values are the number of moves made, the final state and
the modified content of the tape.
Let's see more details in a report of the moves.
In such a report the new content of the tape is shown as
@tt{((head ...) (current tail ...))} where @tt{current} is the current element.
The following machine replaces the second and the fourth tape-element.

@interaction[
(require racket "make-TM.rkt")
(code:line)
(define TM
 (make-TM
  'A      (code:comment "The initial state.")
  '(E)    (code:comment "The final state.")
  'empty
  'blank
  '_      (code:comment "The dummy.")
  '(((A _) ((B) (_  ) R))
    ((B _) ((C) (is ) R))
    ((C _) ((D) (_  ) R))
    ((D _) ((E) (new) N)))))
(code:line)
(TM '(What was your previous hobby?) #:report #t)]

@section{Additional registers}

Every Turing machine emulated by a procedure made by @rack[make-TM]
has at least one state-register and at least one data-register,
but the control unit may have more state- and data-registers.
The first data-register is the input/output-register and is used for exchange of data with the
read/write-head via the data-bus.
A data-register always contains a tape-element.
A state-register always contains a state.
At the start of a move, the current element of the tape is put into the input/output-register.
Subsequently the rule to be applied is determined by the combination of the content
of the first state-register and that of the input/output-register.
During a move new states can be put into the state-registers, possibly obtained from other
state-registers. Likewise new data can be put into the data-registers or be exchanged between them.
After all registers have been updated,
the element in the input/output-register is written onto the tape
such as to replace the current element.
However, if the element to be written is an empty element, a blank is written.
Finally the read/write-head may be moved one step to the right or to the left.
A Turing machine repeats moves until the first state-register contains a final state.

A Turing machine with more than one state-register and/or more than one data-register
is equivalent to a Turing machine with only one state-register and one data-register
as long as the the combined contents of the registers is limited to a finite set.
Allowing more state- and data-registers is a way to simplify the description of the rules.
It allows us to describe a finite multitude of rules in one single line.
For example, multiple registers make it easier to describe rules that move part of the content
of the tape to another position on the tape. Section @secref["More registers"] shows an example.

@section{Procedure make-TM}
@defform-remove-empty-lines[@defform[#:kind "procedure"
(make-TM initial-state final-states empty-element blank dummy
          rules state-registers data-registers name)
#:grammar(
(initial-state   state)
(final-states    (final-state ...))
(final-state     state)
(rules           (rule ...))
(rule            ((old-state old-element) ((new-state ...) (new-element ...) move)))
(old-state       state)
(old-element     tape-element dummy)
(new-state       state state-register-name dummy)
(new-element     tape-element data-register-name dummy)
(state-registers (code:line @#,(element "roman" "optional =") 1)
                 (code:line #:state-registers (state-register-name ...))
                 (code:line #:state-registers @#,(rack exact-positive-integer?)))
(data-registers  (code:line @#,(element "roman" "optional =") 1)
                 (code:line #:data-registers (data-register-name ...))
                 (code:line #:data-registers @#,(rack exact-positive-integer?)))
(name            (code:line @#,(element "roman" "optional =") @#,(rack 'TM-without-name))
                 (code:line #:name @#,(rack symbol?)))
(tape-element    tape-symbol empty-element))
#:contracts ((empty-element (not/c keyword?))
             (blank (not/c keyword?))
             (dummy (not/c keyword?))
             (state (and/c (not/c dummy) (not/c keyword?)))
             (tape-element (and/c (not/c dummy) (not/c keyword?)))
             (state-register-name keyword?)
             (data-register-name keyword?)
             (move (or/c 'R 'L 'N))
             (tape-symbol (not/c (or/c keyword? empty-element dummy))))]{
Procedure @rack[make-TM] returns a procedure that emulates a Turing machine.
Providing an @racketlink[exact-positive-integer? "exact positive integer"] @tt{n}
for @rack[state-registers] or @rack[data-registers] is the same as
@nonbreaking{@rack['(#:0 #:1 ... #:n-1)]}.
Before the machine is produced the arguments are checked to satisfy all contracts
and the following conditions,
equality or being distinct to be understood in the sense of @rack[equal?].

@itemlist[#:style 'ordered
 @item{The @rack[blank], the @rack[empty-element] and the @rack[dummy] must be distinct.}
 @item{The @rack[final-states] must not include an @rack[old-state].}
 @item{The @rack[final-states] must not contain duplicates.                       }
 @item{The @rack[rules] must have distinct combinations @rack[(old-state old-element)].}
 @item{Every @rack[rule] must have as many @rack[new-state]s as @rack[state-register-name]s.}
 @item{Every @rack[rule] must have as many @rack[new-element]s as @rack[data-register-name]s.}
 @item{The list of @rack[state-register-name]s must not contain duplicates.}
 @item{The list of @rack[data-register-name]s must not contain duplicates.}
 @item{Every @rack[new-state] given as a keyword must be one of the @rack[state-register-name]s.}
 @item{Every @rack[new-element] given as a keyword must be one of the @rack[data-register-name]s.}]

When not all of these conditions are satisfied,
procedure @rack[make-TM] raises an @rack[error].
A @rack[rule] is interpreted as follows,
equality again to be understood in the sense of @rack[equal?].
The first one of the @rack[state-registers] will be referred to as the rule-selector-state-register.
Its contents will be referred to as the current rule-selector-state.
The first one of the @rack[data-registers] is the input/output-register.
It contains the @rack[tape-element] read from or to be written onto
the current element under the read/write-head.

@itemlist[#:style 'ordered
@item{A Turing machine halts when the rule-selector-state equals one of the @rack[final-states].}
@item{A @rack[rule] applies if its @rack[old-state] equals the current rule-selector-state
and the @rack[old-element] matches the current element.}
@item{The @rack[dummy] matches every current element.
Every other @rack[old-element] matches only when equal to the current element.}
@item{A @rack[rule] whose @rack[old-element] equals the current element
prevails over a @rack[rule] with the same @rack[old-state] and
whose @rack[old-element] is the @rack[dummy].
For each set of @rack[rules] with the same @rack[old-state] the @rack[dummy]
is like @rack[else] in a @rack[cond]-form,
but is not required to be at the end.
The order of the @rack[rules] is irrelevant.}
@item{When no matching rule can be found, the machine halts by raising an error.}
@item{The first step of a move is putting the current element in the input/output-register.}
@item{The second step puts the @rack[new-state]s in the corresponding @rack[state-registers].
When a @rack[new-state] is a keyword, id est the name of a state-register,
the old content of that register is put in the state-register
corresponding to the position of the @rack[new-state] in the list of @rack[new-state]s.
When a @rack[new-state] is a dummy, the @rack[state] in the corresponding state-register
remains as it is.
In all other cases the @rack[new-state] is stored in the corresponding state-register.
For example, @rack[(#:1 #:0)] indicates that the two registers exchange their contents.
As another example:
@rack[(#:1 whatever)] means that the old contents of register @rack[#:1] must be put into
register @rack[#:0] and that @rack['whatever] must be put in register @rack[#:1].}
@item{In the same way new @rack[tape-element]s are put in the @rack[data-registers].}
@item{Now the @rack[tape-element] of the input/output-register is written on the tape,
replacing the current element.
If the @rack[tape-element] offered to be written is the @rack[empty-element]
a @rack[blank] is written.}
@item{The read/write-head may be moved:@(linebreak)
@rack[move] @rack['L] : move one step to the left.@(linebreak)
@rack[move] @rack['R] : move one step to the right.@(linebreak)
@rack[move] @rack['N] : no move.@(linebreak)
When the read/write-head leaves the current content of the tape,
an @rack[empty-element] is added and the read/write-head is positioned at this element.}
@item{The above process is repeated until the rule-selector-state equals a @rack[final-state].}]

@section{Running a Turing machine}
A procedure returned by procedure @rack[make-TM],
say @(bold (element 'tt "Turing-machine")),
can be called as follows:

@defproc[#:link-target? #f
(Turing-machine
 (input (listof tape-symbol))
 (#:state-registers states (listof state) #f)
 (#:data-registers datums (listof tape-element) #f)
 (#:report report (or/c boolean? 'long 'short) #f)
 (#:limit limit (or/c exact-positive-integer? #f) #f))
(values nr-of-moves final-state output)]{
@rack[nr-of-moves] : @rack[exact-nonnegative-integer?]@(linebreak)
@rack[output] : @rack[(listof tape-symbol)]@(linebreak)@(linebreak)
The @rack[output] is the final content of the tape but without heading or trailing
@rack[empty-element] or @rack[blank]s.
It can contain @rack[blank]s, but not at the begin nor at the end.

If @rack[states] is @rack[#f] all @rack[state-registers] are initialized with the
@rack[initial-state]. Otherwise it must be a list of as many @rack[state]s
as the Turing machine has @rack[state-registers] and
the latter are initialized with the @rack[states]. 

If @rack[datums] is @rack[#f] all @rack[data-registers] are initialized
with the @rack[empty-element].
Otherwise it must be a list of as many @rack[tape-element]s
as the Turing machine has @rack[data-registers] and
the latter are initialized with the @rack[datums].

If @rack[report] is @rack[#t] or @rack['long] the Turing machine
prints a long record of the moves it makes (on the @racket[current-output-port])
For each move the report shows:

@itemlist[#:style 'ordered
@item{The move counter, starting from 1.}
@item{The @rack[rule] being applied.}
@item{The original and new contents of the @rack[state-registers].}
@item{The original and new contents of the @rack[data-registers],
      the original contents of the input/output-register already showing the tape-symbol
      just read from the tape.}
@item{The @rack[move] of the read/write-head (@rack['R], @rack['L] or @rack['N]).}
@item{The new position of the read/write-head and the new content of the tape shown as
@tt{((h ...) (c t ...))},
where the new position of the read/write-head is at element @tt{c}.}]

If @rack[report] is @rack['short] the Turing machine
prints a short record of the moves it makes (on the @racket[current-output-port])
For each move the report shows the move-counter
the old and new state of the first state-register and the new content of the tape.

When @rack[limit] is an @racketlink[exact-positive-integer? "exact positive integer"]
the @tt{Turing-machine} halts by raising an error
when no @rack[final-state] is entered within @rack[limit] moves.
                                                 
@section{Halting problem}
Many Turing machines never halt.
Sometimes this can be predicted by looking at the @rack[rules] only,
sometimes by inspection of both the @rack[rules] and the @rack[input].
However, because of the
@hyperlink["https://en.wikipedia.org/wiki/Halting_problem"]{Halting Problem}
there always remain cases for which it is impossible to detect an infinite loop.
Procedure @rack[make-TM] and the
Turing machines
it produces do no checks at all against infinite loops.
Whether or not a Turing machine halts may depend on its input.
Argument @rack[limit] provides protection.
The following trivial Turing machine
clearly would loop forever with arbitrary input when it would not be halted by
the @rack[limit]:

@interaction[
(require racket "make-TM.rkt")
(define TM (make-TM
            'A   (code:comment "initial state")
            '(T) (code:comment "final states")
            'E   (code:comment "empty cell")
            'B   (code:comment "blank")
            '_   (code:comment "dummy")
            '(((A _) ((A) (_) N)))
            #:name 'Non-halting-TM))
(TM '(B) #:report #t #:limit 5)]

In this example @rack[rule] @rack['(((A _) ((A) (_) N)))] alone already implies an infinite loop.
While the @rack[TM] is running,
its state (the content of the tape and the position of the read/write-head included)
never changes,
which could be detected while the @rack[TM] is running.
However, @rack[TM] does no such check.
As another example consider:

@interaction[
(require racket "make-TM.rkt")
(define TM (make-TM
            'A     (code:comment "initial state")
            '(T)   (code:comment "final state")
            'empty (code:comment "empty cell")
            'blank (code:comment "blank")
            '_     (code:comment "dummy")
            '(((A _) ((A) (blank) R)))
            #:name 'Another-non-halting-TM))
(code:line)
(TM '(whatever) #:report #t #:limit 5)]

By means of mathematical induction it is easily proven that the above machine never halts,
although it never reproduces the same state.

@note{Procedure @rack[make-TM] could be adapted such as to
predict the infinite loops of the last two examples just by checking the rules.
It also could be adapted such as to produce
Turing machines
that can detect a repeated state. These adaptations have not been made,
for the Halting Problem implies that there always remain cases
in which a non-halting case cannot be predicted
by procedure @rack[make-TM] and cannot be detected while a
Turing machine with given @rack[input] is running.}}}]

@section{Examples}

Some of the examples are inspired by material of Jay McCarthy
that can be found in @hyperlink["http://jeapostrophe.github.io/2013-10-29-tmadd-post.html"
                                "http://jeapostrophe.github.io/2013-10-29-tmadd-post.html"].

@subsection{Erase elements}
The following Turing machine always halts.
A correct input is @tt["(x ... [+ x ...] ...)"],
where the square brackets indicate an optional part of the input.
The result of a correct input is the input without @tt["+"].
This is like addition of zero, one or more natural numbers,
where natural number n is written as `@tt["x ..."]' with n @tt["x"]s.
With a correct input the machine halts with @itel{final-state} @tt["T"].
With incorrect input the machine halts with @itel{final-state} @tt["F"].
The machine never moves left of the start of the input.

@interaction[
(require racket "make-TM.rkt")
(code:line)
(define rules
'((code:comment "       State 0 : Inspect the very first element.")
  (code:comment "                 Mark start x with y or start + with p.")
  (code:comment "                 This way we can detect the start of the input")
  (code:comment "                 when moving left and avoid moving left")
  (code:comment "                 of the start of the input.")
  ((0 x) ((1) (y) R))  (code:comment "Ok, go check the remainder of the input.")
  ((0 +) ((1) (p) R))  (code:comment "Ok, go check the remainder of the input.")
  ((0 E) ((T) (B) N))  (code:comment "Empty input accepted.")
  ((0 _) ((F) (_) N))  (code:comment "Reject incorrect input.")
  (code:comment "       State 1 : Check the remainder of the input.")
  ((1 x) ((1) (x) R))  (code:comment "Ok, continue the check.")
  ((1 +) ((1) (+) R))  (code:comment "Ok, continue the check.")
  ((1 E) ((2) (B) L))  (code:comment "Input is ok. Start the addition.")
  ((1 _) ((F) (_) N))  (code:comment "Reject incorrect input.")
  (code:comment "       State 2 : Do the addition from right to left.")
  (code:comment "                 When entering state 2 the read/write-head")
  (code:comment "                 is at the right-most non-blank element.")
  ((2 x) ((2) (x) L))  (code:comment "Leave x as it is and continue addition.")
  ((2 y) ((T) (x) N))  (code:comment "Start of input reached. Done.")
  ((2 +) ((3) (x) R))  (code:comment "Replace + by x and go replacing the last x by a blank.")
  ((2 p) ((3) (y) R))  (code:comment "Replace p by y and go replacing the last x by a blank.")
  (code:comment "       State 3 : Go to end of tape.")
  ((3 x) ((3) (x) R))  (code:comment "Keep looking for end of input.")
  ((3 B) ((4) (B) L))  (code:comment "End of input reached.")
  (code:comment "       State 4 : Replace the last x (or the y if there is no x) by a blank.")
  ((4 x) ((2) (B) L))  (code:comment "Replace x by a blank and continue addition.")
  ((4 y) ((T) (B) N))  (code:comment "Replace y by a blank and accept.")))
(code:line)
(define TM (make-TM
            '0     (code:comment "initial state")
            '(T F) (code:comment "final states")
            'E     (code:comment "empty cell")
            'B     (code:comment "blank")
            '_     (code:comment "dummy")
            rules))
(code:line)
(TM '(x + x x + x x x) #:report 'short)]

@subsection{Binary addition}
The following Turing machine adds two natural numbers written in binary notation.
The machine halts with every arbitrary input.
A correct input is defined as follows:

@inset{@verbatim[
"input   = (operand + operand)
operand = bit bit ...
bit     = 0 | 1"]}

An incorrect input yields @itel{final-state} @element['tt "F"].
A correct input yields @itel{final-state} @element['tt "T"] and @tt{output}
@nonbreaking{@rack[(bit bit ...)]}
showing the sum of the two operands.
More precisely the @tt{output} is @nonbreaking{@rack[(1 bit ...)]} or @rack[(0)],
id est, without leading zeros.
The initial content of the tape is modified such as to result in the sum.
In the sum a 0 bit is written as @element['tt "x"] and a 1 bit as @element['tt "y"]
such as to know which bits already have been established and which ones yet have to be computed.
During the addition the content of the tape is (ignoring blanks and empty-element) 
@nonbreaking{@element['tt "(0-or-1 ... x-or-y ... + 0-or-1 ...)"]}.
Bits of the second operand are processed starting from the least significant one.
Every such bit is replaced by a @itel["blank"] before it is processed.
The significance of the blanked bit is the same as that of
the right-most bit @nonbreaking{@element['tt "0-or-1"]} of the first operand.
After all bits of the second operand have been processed,
the @element['tt "+"] is removed,
elements @element['tt "x"] and @element['tt "y"] are reverted to
@element['tt "0"] and @element['tt "1"] and leading zeros are removed.

@interaction[
(require racket "make-TM.rkt")
(code:line)
(define rules
'((code:comment "Check the input.")
  (code:comment "At least one bit required preceding +.")
  ((0 0) ((1) (0) R)) (code:comment "Ok, continue parsing the first operand.")
  ((0 1) ((1) (1) R)) (code:comment "Ok, continue parsing the first operand.")
  ((0 _) ((F) (_) N)) (code:comment "Reject.")
  (code:comment "Check the remainder of the first operand.")
  ((1 0) ((1) (0) R)) (code:comment "Continue checking the first operand.")
  ((1 1) ((1) (1) R)) (code:comment "Continue checking the first operand.")
  ((1 +) ((2) (+) R)) (code:comment "End of first operand, go to second operand.")
  ((1 _) ((F) (_) N)) (code:comment "Reject.")
  (code:comment "At least one bit required for the second operand.")
  ((2 0) ((3) (0) R)) (code:comment "Ok, continue parsing the second operand.")
  ((2 1) ((3) (1) R)) (code:comment "Ok, continue parsing the second operand.")
  ((2 _) ((F) (_) N)) (code:comment "Reject.")
  (code:comment "Check the remainder of the second operand.")
  ((3 0) ((3) (0) R)) (code:comment "Ok, continue parsing the second operand.")
  ((3 1) ((3) (1) R)) (code:comment "Ok, continue parsing the second operand.")
  ((3 E) ((4) (B) L)) (code:comment "End of correct input. Go to the addition.")
  ((3 _) ((F) (_) N)) (code:comment "Reject.")
  (code:comment "Addition")
  (code:comment "We are at the least significant bit of the second operand.")
  ((4 0) ((5) (B) L)) (code:comment "Erase the bit and add it to the first operand.")
  ((4 1) ((7) (B) L)) (code:comment "Erase the bit and add it to the first operand.")
  (code:comment "Adding bit 0.")
  (code:comment "Look for the least significant bit of the first operand.")
  ((5 +) ((6) (+) L)) (code:comment "Least significant bit of first operand found.")
  ((5 _) ((5) (_) L)) (code:comment "Continue looking for first operand.")
  ((6 x) ((6) (x) L)) (code:comment "Skip bits already computed.")
  ((6 y) ((6) (y) L)) (code:comment "Skip bits already computed.")
  ((6 0) ((A) (x) R)) (code:comment "Mark bit as having been computed.")
  ((6 1) ((A) (y) R)) (code:comment "Mark bit as having been computed.")
  ((6 E) ((A) (x) R)) (code:comment "Add a bit marked as having been computed.")
  ((6 B) ((A) (x) R)) (code:comment "Add a bit marked as having been computed.")
  (code:comment "Adding bit 1.")
  (code:comment "Look for the least significant bit of the first operand.")
  ((7 +) ((8) (+) L)) (code:comment "Least significant bit of first operand found.")
  ((7 _) ((7) (_) L)) (code:comment "Continue looking for first operand.")
  ((8 x) ((8) (x) L)) (code:comment "Skip bits already computed.")
  ((8 y) ((8) (y) L)) (code:comment "Skip bits already computed.")
  ((8 0) ((A) (y) R)) (code:comment "Put a 1 bit as having been computed.")
  ((8 1) ((9) (x) L)) (code:comment "Put a zero bit as being computed and process carry.")
  ((8 B) ((A) (y) R)) (code:comment "Add the bit.")
  ((8 E) ((A) (y) R)) (code:comment "Add the bit.")
  (code:comment "Process a carry.")
  ((9 0) ((A) (1) R))
  ((9 1) ((9) (0) L))
  ((9 B) ((A) (1) R))
  ((9 E) ((A) (1) R))
  (code:comment "Go to next least significant bit of second operand.")
  ((A B) ((B) (B) L)) (code:comment "End of second operand.")
  ((A _) ((A) (_) R)) (code:comment "Keep on looking.")
  (code:comment "Here we are at the least significant bit of the second operand.")
  ((B 0) ((5) (B) L)) (code:comment "Remove bit from the second operand and go add it.")
  ((B 1) ((7) (B) L)) (code:comment "Remove bit from the second operand and go add it.")
  ((B +) ((C) (B) L)) (code:comment "Second operand totaly processed. Erase the + sign.")
  (code:comment "Addition is complete.")
  (code:comment "Revert x to 0 and y to 1.")
  ((C x) ((C) (0) L))
  ((C y) ((C) (1) L))
  ((C 0) ((C) (0) L))
  ((C 1) ((C) (1) L))
  ((C B) ((D) (B) R))
  ((C E) ((D) (B) R))
  (code:comment "Remove heading zeros, but make sure at least one bit remains.")
  ((D 0) ((D) (B) R))
  ((D 1) ((T) (1) N))
  ((D B) ((T) (0) N))
  ((D E) ((T) (0) N))))
(code:line)
(define adder (make-TM
               '0     (code:comment "initial state")
               '(T F) (code:comment "final states")
               'E     (code:comment "empty cell")
               'B     (code:comment "blank")
               '_     (code:comment "dummy")
               rules))
(code:line)
(adder '(1 0 1 1 + 1 0 1 1 1) #:report 'short)
(code:line)
(adder '(0 0 0 1 1 + 0 0 1 1))
(code:line)
(adder '(0 0 0 + 0 0))
(code:line)
(code:comment "Checking the Turing machine.")
(code:comment "We need two procedures for conversion between")
(code:comment "exact nonnegative integer numbers and lists of bits.")
(code:line)
(code:comment "Procedure exact-nonnegative-integer->list-of-bits converts")
(code:comment "exact nonnegative integer n to a list of bits 0 and 1.")
(code:line)
(define (exact-nonnegative-integer->list-of-bits n)
 (reverse
  (let loop ((n n))
   (cond
    ((zero? n) '(0))
    ((even? n) (cons 0 (loop (quotient n 2))))
    (else      (cons 1 (loop (quotient n 2))))))))
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
(code:comment "Test the Turing machine.")
(code:line)
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
It replaces each @itel{tape-symbol} @nonbreaking{@element['tt "(n m)"]} by one decimal digit.
State @element['tt "0"] indicates that there is no carry.
State @element['tt "1"] indicates that a carry must be added.
State @element['tt "0"] is the initial internal state and @element['tt "T"] the final state.

@interaction[
(require racket "make-TM.rkt")
(code:line)
(define rules
 (append
  (list
   '((0 E) ((T) (B) R))
   '((1 E) ((T) (1) R)))
  (for*/list
   ((c (in-range 0 2))  (code:comment "0 = no carry, 1 = carry")
    (n (in-range 0 10)) (code:comment "digit of first operand")
    (m (in-range 0 10)) (code:comment "digit of second operand"))
   (define-values (q r) (quotient/remainder (+ n m c) 10))
   `((,c (,n ,m)) ((,q) (,r) R)))))
(code:line)
(pretty-print rules)
(code:line)
(define TM (make-TM
            0    (code:comment "initial state")
            '(T) (code:comment "final state")
            'E   (code:comment "empty cell")
            'B   (code:comment "blank")
            '_   (code:comment "dummy")
            rules))
(code:line)
(call-with-values
 (λ () (TM (reverse (map list '(0 0 9) '(0 0 9)))))
 (λ (nr-of-moves final-state output)
  (values nr-of-moves final-state (reverse output))))
(code:line)
(code:comment "nr->lst takes an exact nonnegative integer and")
(code:comment "returns its list of digits from least to most significant one.")
(code:line)
(define (nr->lst n)
 (define (nr->lst n)
  (cond
   ((zero? n) '())
   (else
    (define-values (q r) (quotient/remainder n 10))
    (cons r (nr->lst q)))))
 (if (zero? n) '(0) (nr->lst n)))
(code:line)
(code:comment "prepare-input takes two exact nonnegative integers")
(code:comment "and returns the corresponding input for TM.")
(code:line)
(define (prepare-input n m)
 (let ((n (nr->lst n)) (m (nr->lst m)))
  (define ln (length n))
  (define lm (length m))
  (define len (max ln lm))
  (map list (append n (make-list (- len ln) 0))
            (append m (make-list (- len lm) 0)))))
(code:line)
(code:comment "output->nr converts the output of the TM")
(code:comment "to an exact nonnegative integer.")
(code:line)
(define (output->nr lst)
 (if (null? lst) 0
  (+ (car lst) (* 10 (output->nr (cdr lst))))))
(code:line)
(let ((n 9876) (m 987654))
 (let-values (((nr-of-moves final-state output) (TM (prepare-input n m) #:report #t)))
  (define sum (output->nr output))
  (values sum (= sum (+ n m)))))
(code:line)
(code:comment "Test the TM.")
(code:line)
(for/and ((k (in-range 0 1000)))
 (define n (random 1000000000))
 (define m (random 1000000000))
 (define-values (nr-of-moves final-state output) (TM (prepare-input n m)))
 (and (= (output->nr output) (+ n m)) (eq? final-state 'T)))]

@subsection{Busy beaver}
3 state busy beaver. In fact there are four states, but @itel{final-state} @tt{T} does not count.

@interaction[
(require racket "make-TM.rkt")
(define rules
 '(((A 0) ((C) (1) R))
   ((A 1) ((A) (1) R))
   ((B 0) ((A) (1) R))
   ((B 1) ((C) (1) L))
   ((C 0) ((B) (1) L))
   ((C 1) ((T) (1) N))))
(define TM
 (make-TM
  'A   (code:comment "The initial state.")
  '(T) (code:comment "The final state.")
  0    (code:comment "The empty-element.")
  'blank-not-used
  'dummy-not-used
  rules))
(TM '() #:report #t)]

4 state busy beaver. In fact there are five states, but @itel{final-state} @tt{T} does not count.

@interaction[
(require racket "make-TM.rkt")
(define rules
 '(((A 0) ((B) (1) R)) ((A e) ((B) (1) R))
   ((B 0) ((A) (1) L)) ((B e) ((A) (1) L))
   ((C 0) ((T) (1) R)) ((C e) ((T) (1) R))
   ((D 0) ((D) (1) R)) ((D e) ((D) (1) R))
   ((A 1) ((B) (1) L))
   ((B 1) ((C) (0) L))
   ((C 1) ((D) (1) L))
   ((D 1) ((A) (0) R))))
(define TM
 (make-TM
  'A   (code:comment "The initial state.")
  '(T) (code:comment "The final state.")
  'e   (code:comment "The empty-element.")
  'blank-not-used
  'dummy-not-used
  rules))
(TM '() #:report 'short)]

@subsection{Zeros and ones}

The following Turing machine halts on every arbitrary input.
If the input is a list of zeros and ones with as many zeros as ones,
the @itel{final-state} is @rack['T].
In all other cases the @itel{final-state} is @rack['F].
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
(require racket "make-TM.rkt")
(code:line)
(define simplified-rules
 '((code:comment "state 0: starting state.")
   (code:comment "Accept empty input, otherwise add starting mark s.")
   ((0 E) (T B N)) (code:comment "Accept empty input.")
   ((0 _) (1 _ L))
   ((1 E) (2 s R))
   (code:comment "state 2: Check that we have 0s and 1s only and add an ending mark e.")
   ((2 0) (2 0 R))
   ((2 1) (2 1 R))
   ((2 E) (3 e N))
   ((2 _) (F _ N))
   (code:comment "state 3: Go to the end of the tape.")
   ((3 e) (4 e L))
   ((3 _) (3 _ R))
   (code:comment "state 4: look for a 0 or a 1 at the left")
   ((4 s) (T B N)) (code:comment "Ok, no more 0s or 1s.")
   ((4 0) (5 e L)) (code:comment "a 1 at the left is required.")
   ((4 1) (6 e L)) (code:comment "a 0 at the left is required.")
   ((4 B) (4 e L))
   (code:comment "state 5: look for a required 1 at the left.")
   ((5 0) (5 0 L)) (code:comment "skip 0.")
   ((5 1) (3 B R)) (code:comment "found.")
   ((5 s) (F s N)) (code:comment "no 1 found.")
   ((5 B) (5 B L))
   (code:comment "state 6: look for a required 0 at the left.")
   ((6 0) (3 B R)) (code:comment "found.")
   ((6 1) (6 1 L)) (code:comment "skip 1.")
   ((6 s) (F s N)) (code:comment "no 0 found.")
   ((6 B) (6 B L))))
(define rules
 (map
  (λ (rule) (match rule ((list (list a b) (list c d e)) `((,a ,b) ((,c) (,d) ,e)))))
  simplified-rules))
(code:line)
(define TM
 (make-TM
  0      (code:comment"initial state")
  '(T F) (code:comment"final states")
  'E     (code:comment"empty cell")
  'B     (code:comment"blank")
  '_     (code:comment"dummy")
  rules))
(code:line)
(TM '(0 1 0 0 1 1 1 0))
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

@subsection{Checking parentheses}

The following machine reads @rack[L] as a left parenthesis
an @rack[R] as a right parenthesis.
The machine halts in state @rack[T] if the parentheses are well balanced
and no other elements occur in the @itel{input}.
In all other cases the machine halts in state @rack[F].
When counting a @rack[L] as @element['tt "+1"] and an @rack[R] as @element['tt "-1"],
going from left to right the addition never must go below zero and must end in zero.
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
(require racket "make-TM.rkt")
(code:line)
(define simplified-rules
  (code:comment "state 0")
  (code:comment "accept empty input.")
  (code:comment "put start marker s before non-empty input.")
'(((0 E) (T B N))
  ((0 _) (1 _ L))
  ((1 E) (2 s R))
  (code:comment "state 2")
  (code:comment "check input.")
  (code:comment "put end marker e at end of input.")
  ((2 L) (2 L R))
  ((2 R) (2 R R))
  ((2 E) (3 e L))
  ((2 _) (F _ N))
  (code:comment "state 3")
  (code:comment "we are at the end of the tape.")
  (code:comment "look left for R immediately preceded by L.")
  ((3 B) (3 B L))
  ((3 s) (7 B R)) (code:comment "all done, go blank the end mark e.")
  ((3 R) (4 R L)) (code:comment "found a R.")
  ((3 _) (F _ N))
  ((4 B) (4 B L))
  ((4 L) (5 B R)) (code:comment "found immediately preceeding L, blank the L.")
  ((4 R) (4 R L)) (code:comment "found another R.")
  ((4 _) (F _ N))
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
  ((7 e) (T B N))
  ((7 _) (7 _ R))))
(code:line)
(define rules
 (map
  (λ (rule) (match rule ((list (list a b) (list c d e)) `((,a ,b) ((,c) (,d) ,e)))))
  simplified-rules))
(code:line)
(define TM (make-TM 0 '(T F) 'E 'B '_ rules))
(code:line)
(code:comment "The following examples yield final state T")
(code:line)
(TM '())
(TM '(L R))
(TM '(L R L R L R))
(TM '(L L L R R R))
(TM '(L L R L R R))
(code:line)
(code:comment "The following examples yield final state F")
(code:line)
(TM '(a))
(TM '(L a R))
(TM '(R))
(TM '(L))
(TM '(R L))
(TM '(R L R L R L R))
(TM '(L R L R L R L))]

@subsection[#:tag "Inserting elements"]{Inserting elements}

The following Turing machine always halts.
For an input consisting of @rack['a]s and @rack['b]s only
the @itel{final-state} is @rack['T] and symbol @rack['x] is inserted
between each @rack['a] and an immediately following @rack['b].
The insertion of @rack['x] requires that the elements
preceding the @rack['b] are shifted one cell to the left.
An input containing anything other than @rack['a] or @rack['b]
yields @itel{final-state} @rack['F].
@rack[0] is the initial state. @rack['B] is the blank.
@rack['E] is the empty cell. @rack['_] is the dummy symbol.

@interaction[
(require racket "make-TM.rkt")
(code:line)
(define simplified-rules
'((code:comment "Look for a.")
  ((0     a) (1     a R))
  ((0     b) (0     b R))
  ((0     E) (T     B N))
  ((0     _) (F     _ N))
  (code:comment "Symbol a found, is next symbol b?")
  ((1     a) (1     a R)) (code:comment "Keep looking for b.")
  ((1     b) (2     M L)) (code:comment "yes, mark it M and proceed.")
  ((1     _) (F     _ N))
  ((1     E) (T     B N))
  (code:comment "Rewind the tape.")
  ((2     E) (3     B R))
  ((2     _) (2     _ L))
  (code:comment "Shift every symbol one cell to the left up to mark M.")
  (code:comment "Replace a or b or x by B.")
  (code:comment "Replace preceding B by a or b or x.")
  (code:comment "Replace M by b and replace preceding B by x.")
  ((3     a) ((4 a) B L))
  ((3     b) ((4 b) B L))
  ((3     x) ((4 x) B L))
  ((3     M) ((4 M) b L))
  (((4 a) B) (5     a R)) (code:comment "Continue the shift.")
  (((4 b) B) (5     b R)) (code:comment "Continue the shift.")
  (((4 x) B) (5     x R)) (code:comment "Continue the shift.")
  (((4 M) B) (0     x R)) (code:comment "Shift completed. Look for next a followed by b.")
  (code:comment "Step to the right of the B and continue the shift.")
  ((5     B) (3     B R))))
(code:line)
(define rules
 (map
  (λ (rule) (match rule ((list (list a b) (list c d e)) `((,a ,b) ((,c) (,d) ,e)))))
  simplified-rules))
(code:line)
(define TM (make-TM  0 '(T F) 'E 'B  '_ rules))
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
(random-seed 0)
(code:line)
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

@subsection{Counter}

Represent natural number n as @tt{x ...} or @tt{y ...} with n @tt{x}s or @tt{y}s.
The following Turing machine never halts.
Given empty input it forms an infinite tape containing the numbers 0, 1, 2 etc.
separated by slashes.
Every next number is formed by putting an @tt{x} at the end of the content
and copying the previous number, which has the form @tt{x ...}.
While copying, the @tt{x}s of the previous number are replaced by @tt{y}s
such as to indicate they already have been copied.

@interaction[
(require racket "make-TM.rkt") 
(code:line)
(define simplified-rules
'((code:comment "Form zero.")
  ((0 E) (1 / R))
  ((1 E) (2 / R))
  (code:comment "Put an x and go add the previous nr.")
  ((2 E) (3 x L))
  (code:comment "First go to end of previous nr.")
  ((3 /) (4 / L))
  ((3 _) (3 _ L))
  (code:comment "Copy x to end of tape.")
  (code:comment "Copied xs are replaced by ys.")
  ((4 x) (5 y R)) (code:comment "Mark x as copied and go put x at end of tape.")
  ((4 y) (4 y L)) (code:comment "y has already been copied. Keep looking for x.")
  ((4 /) (6 / R)) (code:comment "Copy is complete.")
  ((5 _) (5 _ R)) (code:comment "Go to end of tape, write x and")
  ((5 E) (3 x L)) (code:comment "continue copying.")
  (code:comment "Next number complete.")
  ((6 _) (6 _ R)) (code:comment "Go to end of tape.")
  ((6 E) (2 / R)) (code:comment "Go form the next nr.")
  ))
(code:line)
(define rules
 (map
  (λ (rule) (match rule ((list (list a b) (list c d e)) `((,a ,b) ((,c) (,d) ,e)))))
  simplified-rules))
(code:line)
(define TM
 (make-TM
 '0   (code:comment "initial state")
 '()  (code:comment "no final state")
 'E   (code:comment "empty cell")
 'blank-not-used
 '_   (code:comment "dummy")
 rules))
(code:line)
(code:comment "Limit the number of moves.")
(code:comment "The error message shows the resulting content of the tape.")
(TM '() #:limit 161 #:report 'short)]

@subsection[#:tag "More registers"]{More registers}
The Turing machines shown sofar in this document have one data-register and
one state-register only.
Let us use a Turing machine with two data-registers to simplify and to speed up
the example of section @secref{Inserting elements}.
One extra data-register is used.
It memorizes the previously replaced element when shifting tape-elements to the left
in order to make space for an x.

@interaction[
(require racket "make-TM.rkt")
(code:line)
(define rules
 '((code:comment "look for a.")
   ((0 a) ((1) (a   empty) R)) (code:comment "a found.")
   ((0 b) ((0) (b   empty) R)) (code:comment "keep looking.")
   ((0 x) ((0) (x   empty) R)) (code:comment "keep looking")
   ((0 E) ((T) (B   empty) N)) (code:comment "all done, halt.")
   ((0 B) ((T) (B   empty) N)) (code:comment "all done, halt.")
   ((0 _) ((F) (B   empty) N)) (code:comment "disallowed input, halt.")
   (code:comment "Is a followed by b?")
   ((1 a) ((1) (a   empty) R)) (code:comment "no, but we have an a, hence continue.")
   ((1 b) ((2) (b   x    ) L)) (code:comment "yes, go insert x and shift elements at the left.")
   ((1 x) ((0) (x   empty) R)) (code:comment "no, go looking for an a.")
   ((1 _) ((T) (B   empty) N)) (code:comment "end of tape, accept.")
   (code:comment "Shift all elements at the left one step to the left.")
   ((2 E) ((0) (#:1 empty) R)) (code:comment "Done, repeat the whole process.")
   ((2 B) ((0) (#:1 empty) R)) (code:comment "Done, repeat the whole process.")
   ((2 _) ((2) (#:1 #:0  ) L)) (code:comment "Keep shifting.")
 ))
(code:line)
(define TM (make-TM  0 '(T F) 'E 'B  '_ rules #:data-registers 2))
(code:line)
(TM '(b a b a b a) #:report #t)
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

@larger{@larger{@bold{The end}}}
