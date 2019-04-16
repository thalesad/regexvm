(** printing [$ %\ensuremath{\llbracket}% *)
(** printing $] %\ensuremath{\rrbracket}% *)
(** printing ** %\ensuremath{\,\mid\,}% *)
(** printing {{ %\ensuremath{\{\kern-0.4ex\{}% *)
(** printing }} %\ensuremath{\}\kern-0.4ex\}}% *)
(** printing sig1 %$\coqdocvar{sig}$% *)
(** printing exist1 %$\coqdocvar{exist}$% *)
(** printing merge1 %$\coqdocvar{merge}$% *)
(** printing Acc1 %$\coqdocvar{Acc}$% *)
(** printing Acc_intro1 %$\coqdocvar{Acc\_intro}$% *)
(** printing well_founded1 %$\coqdocvar{well\_founded}$% *)

(* begin hide *)
Set Implicit Arguments.
(* end hide *)

(**

* Introduction
%\label{sec:intro}%

We name parsing the process of analyzing if a sequence of symbols matches a given set of rules.
Such rules are usually specified in a formal notation, like a grammar. If a string can be obtained
from those rules, we have success: we can build some evidence that the input is in the language
described by the underlying formalism. Otherwise, we have a failure: no such evidence exists.

In this work, we focus on the parsing problem for regular expressions (REs), which are an algebraic
and compact way of defining regular languages (RLs), i.e., languages that can be recognized by
(non-)deterministic finite automata and equivalent formalisms. REs are widely used in string search
tools, lexical analyser generators and XML schema languages %\cite{Frisch2004}%. Since RE parsing
is pervasive in computing, its correctness is crucial and is the subject of study of several
recent research works (e.g %\cite{Firsov13,Ribeiro2017,Lopes2016,Asperti10}%).

Approaches for RE parsing can use representations of finite state machines (e.g. %\cite{Firsov13}%),
derivatives (e.g. %\cite{Ribeiro2017,Lopes2018,Lopes2016}%) or the so-called pointed RE's or its
variants %\cite{Asperti10,Fischer2010}%. Another approach for parsing is based on the so-called
parsing machines, which dates back to 70's with Knuth's work
on top-down syntax analysis for context-free languages %\cite{Knuth71}%. Recently, some works
have tried to revive the use of such machines for parsing: Cox %\cite{Cox2009}% defined a VM
for which a RE can be seen as ``high-level programs'' that can be compiled to a sequence of
such VM instructions and Lua library LPEG %\cite{Ierusalimschy2009}% defines a VM whose instruction
set can be used to compile Parser Expressions Grammars (PEGs) %\cite{Ford04}%. Such renewed research
interest is motivated by the fact that is possible to include new features by just adding and
implementing new machine instructions.

Since LPEG VM is designed with PEGs in mind, it is not appropriate for RE parsing, since the ``star''
operator for PEGs has a greedy semantics which differs from the conventional RE semantics for this operator. 
Also, Cox's work on VM-based RE parsing has problems. First, it is poorly specified: both the VM semantics 
and the RE compilation process are described only informally and no correctness guarantees is even mentioned. 
Second, it does not provide an evidence for matching, which could be used to characterize a disambiguation 
strategy, like Greedy %\cite{Frisch2004}% and POSIX %\cite{Sulzmann14}%. To the best of our knowledge, no 
previous work has formally defined a VM for RE parsing that produces evidence (parse trees) for successul matches.
The objective of this work is to give a first step in filling this gap. More specifically, we are interested in formally
specify and prove the correctness of a VM based semantics for RE parsing which produces bit-codes as
a memory efficient representation of parse-trees. As pointed by %\cite{Lasse2011}%, bit-codes are useful because they
are not only smaller than the parse tree, but also smaller than the string being parsed and they can be combined with methods
for text compression. We would like to emphasize that, unlike Cox's work, which develop its VM using a instruction 
set like syntax and semantics, we use, as inspiration, virtual machines for the %$\lambda$%-calculus, like the 
SECD and Krivine machines %\cite{Krivine07,Landin64}%. 

One important issue regarding RE parsing is how to deal with the so-called problematic 
RE%\footnote{We say that a RE $e$ is problematic if there's exists $e_1$ s.t. $e = e_1^\star$ and 
$e_1$ accepts the empty string.}\cite{Frisch2004}%. In order to avoid the well-known issues with 
problematic RE, we use a transformation proposed by Medeiros et. al.%\cite{Medeiros14}% which turns a
problematic RE into equivalent non-problematic one. We prove that this algorithm indeed produce
equivalent REs using Coq proof assistant.

Our contributions are:

- We present a big step semantics for a VM for RE parsing which produces bit-codes as parsing evidence.

- We developed a certified implementation of an algorithm that converts a problematic RE into a 
  non-problematic one.

- We proved that the bit-codes produced by our VM are valid parsing evidence.

- We extract from our formalization a certified algorithm in Haskell and use it 
  to build a RE parsing tool. We compare the its performance against 
  well known Haskell libraries for RE parsing.  

This paper describes the continuation of the RE VM-based parsing research which we previously reported 
on a paper published on SBLP 2018 %\cite{Delfino18}%. The current work improves our previous results
mainly by: 1) using a big-step operational semantics which deals correctly with problematic RE, unlike
our previous small-step semantics; 2) all results of this paper are completely mechanized using Coq
proof assistant. Our previous work used property-based testing in order to provide an evidence of 
the correctness of the small-step semantics.    

The rest of this paper is organized as follows. Section %\ref{section:coq}% gives a 
suscint introduction to Coq proof assistant. Section %\ref{section:background}% presents some 
background concepts on RE and its parsing problem. 
Our operational semantics for RE parsing and its theoretical properties
are described in Section %\ref{section:semantics}%. Our Coq formalization is described in 
Section %\ref{section:formalization}%. Section %\ref{section:related}% discuss related work and Section 
%\ref{section:experiments}% presents some experimental results with the tool produced using the 
verified algorithm. Finally, Section %\ref{section:conclusion}% concludes and 
presents some directions for future work.

While all the code on which this paper is based has been developed in Coq,
we adopt a ``lighter'' syntax in the presentation of its code fragments. 
We chose this presentation style in order to improve readability, because
 functions that use dependently typed pattern matching require a high number of type
annotations, that would deviate from our objective of providing a formalization 
that is easy to understand. For theorems and lemmas, we sketch the proof strategy 
but omit tactic scripts.  All source code produced, including the source of this article, 
instructions on how to build it and reproduce the reported experiments are avaliable 
on-line %\cite{regexvm-rep}%.

* A tour of Coq proof assistant
%\label{section:coq}%

Coq is a proof assistant based on the calculus of inductive
constructions (CIC) %\cite{Bertot2010}%, a higher-order typed
%$\lambda$%-calculus extended with inductive definitions. Theorem
proving in Coq follows the ideas of the so-called
``BHK-correspondence''%\footnote{Abbreviation of Brower, Heyting,
  Kolmogorov, de Bruijn and Martin-L\"of Correspondence. This is also
  known as the Curry-Howard ``isomorphism''.}%, where types represent
logical formulas, %$\lambda$%-terms represent proofs, and the task of
checking if a piece of text is a proof of a given formula corresponds
to type-checking (i.e. checking if the term that represents the proof
has the type corresponding to the given formula) %\cite{Sorensen2006}%.

Writing a proof term whose type is that of a logical formula can be
however a hard task, even for simple propositions.  In order to make
this task easier, Coq provides %\emph{tactics}%, which are commands that
can be used to help the user in the construction of proof terms.

In this section we provide a brief overview of Coq. We start with the
small example, that uses basic
features of Coq --- types, functions and proof definitions.  In this
example, we use an inductive type that represents natural numbers in
Peano notation. The [nat] type definition includes an
annotation, that indicates that it belongs to the [Set]
sort%\footnote{Coq's type language classifies new inductive (and
  co-inductive) definitions by using sorts. [Set] is the sort
  of computational values (programs) and [Prop] is the sort of
  logical formulas and proofs.}%. Type [nat] is formed by two
data constructors: [O], that represents the number %$0$%, and [S],
the successor function.
 *)

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Fixpoint plus (n m : nat) : nat :=
   match n with
   | O => m
   | S n' => S (plus n' m)
   end.

Theorem plus0r : forall n, plus n 0 = n.
Proof.
   intros n. induction n.
   reflexivity.
   simpl. rewrite -> IHn. reflexivity.
Qed.

(**
Command [Fixpoint] allows the definition of functions by
structural recursion. The definition of [plus], for summing two
values of type [nat], is straightforward. It should be noted
that all functions defined in Coq must be total.

Besides declaring inductive types and functions, Coq allows us to
define and prove theorems. In our exemple, we show a simple theorem
about [plus], that states that
[plus n 0 = n], for an arbitrary value [n] of type
[nat]. Command [Theorem] allows the statement of a
formula that we want to prove and starts the %\emph{interactive proof mode}%, 
in which tactics can be used to produce the proof term that
is the proof of such formula. In the example, various tactics are
used to prove the desired result.  The first tactic, [intros], is
used to move premisses and universally quantified variables from the
goal to the hypothesis. Tactic [induction] is used to start an inductive
proof over an inductively defined object (in our example,
the natural number [n]), generating a case for each constructor and
an induction hypothesis for each recursive branch in constructors.
Tactic [reflexivity] proves trivial equalities up to conversion and
[rewrite] is used to replace terms using some equality. 

For each inductively defined data type,
Coq generates automatically an induction principle %\cite[Chapter
  14]{Bertot2010}%. For natural numbers, the following Coq term, called
[natind], is created: 
*)

natind
     : forall P : nat -> Prop,
       P O -> (forall n : nat, P n -> P (S n)) ->
       forall n : nat, P n
(**
It expects a property ([P]) over natural numbers (a value of type
[nat -> Prop]), a proof that [P] holds for zero (a value of
type [P 0]) and a proof that if [P] holds for an arbitrary
natural [n], then it holds for [S n] (a value of type
[forall n:nat, P n -> P (S n)]). Besides [natind], generated by
the use of tactic [induction], the term below 
uses the constructor of the equality
type [eqrefl], created by tactic [reflexivity], and term
[eqindr], inserted by the use of tactic [rewrite]. Term
[eqindr] allows concluding [P y] based on the assumptions
that [P x] and [x = y] are provable.
 *)
                  
plus0rterm :=
	fun n : nat =>
		natind
		(fun n0 : nat => plus n0 O = n0) (eqrefl O)
		  (fun (n' : nat) (IHn' : plus n' O = n') =>
		   eqindr (fun n0 : nat => S n0 = S n')
		     (eqrefl (S n')) IHn') n
		: forall n : nat, plus n O = n
                                         
(**
Instead of using tactics, one could instead write CIC terms directly
to prove theorems.  This can be however a complex task, even for
simple theorems like [plus0r], because it generally requires
detailed knowledge of the CIC type system.

An interesting feature of Coq is the possibility of defining inductive
types that mix computational and logical parts. Such types are usually
called %\emph{strong specifications}%, since they allow the definition
of functions that compute values together with a proof that this value
has some desired property. As an example, consider type [sig]
below, also called ``subset type'', that is defined in Coq's standard
library as:
 *)

Inductive sig (A : Set)	(P : A -> Prop) : Set :=
 | exist : forall x : A, P x -> sig A P.

(** 
Type [sig] is usually expressed in Coq by using the following
syntax: %$\{x : A \,\vert\,P\:x\}$%
Constructor [exist] has two
parameters. Parameter [x : A] represents the
computational part. The other parameter, of type [P x], denotes
the ``certificate'' that [x] has the property specified by
predicate [P]. As an example, consider:
[[
forall n : nat, n <> 0 -> {m | n = S m}
]]
This type can be used to specify a function that returns the
predecessor of a natural number [n], together with a proof that
the returned value really is the predecessor of [n]. The
definition of a function of type [sig] requires the specification
of a logical certificate. As occurs in the case of theorems, tactics
can be used in the definition of such functions. For example, a
definition of a function that returns the predecessor of a given
natural number, if it is different from zero, can be given as follows:
 *)

Definition predcert : forall n : nat, n <> 0 -> {m | n = S m}.
   intros n H.
   destruct n.
   destruct H. reflexivity.
   exists n. reflexivity.
Defined.

(**
Tactic [destruct] is used to start a proof by case analysis on
structure of a value.

Another example of a type that can be used to provide strong
specifications in Coq is [sumor], that is defined in the
standard library as follows:
 *)

Inductive sumor(A : Set) (B : Prop) : Set :=
| inleft : A -> sumor A B
| inright : B -> sumor A B.

(**
Coq standard library also provides syntactic sugar (or, in Coq's
terminology, notations) for using this type: ``[sumor A B]'' can
be written as [A + {B}].
This type can be used as the type of a function that returns either a
value of type [A] or a proof that some property specified by
[B] holds.
As an example, we can specify the type of a function that returns a
predecessor of a natural number or a proof that the given number is
equal to zero as follows, using type [sumor]:
[[
{p | n = S p} + {n = 0}
]]
A common problem when using rich specifications for functions is the need
of writing proof terms inside its definition body. A possible solution for
this is to use the [refine] tactic, which allows one to specify a term with
missing parts (knowns as ``holes'') to be filled latter using tactics.

The next code piece uses the [refine] tactic to build the computational part
of a certified predecessor function. We use holes to mark positions where proofs are
expected. Such proof obligations are later filled by tactic [reflexivity] which finishes
[predcert] definition.
 *)

Definition predcert : forall n : nat, {p | n = S p} + {n = 0}.
  refine (fun n =>
            match n with
            | O => inright _
            | S n' => inleft _ (exist _ n' _)
            end) ; reflexivity.
Defined.

(**

A detailed discussion on using Coq is out of the scope of this paper. Good introductions
to Coq proof assistant are avaliable elsewhere %\cite{Bertot2010,Chlipala13}%.

* Background
%\label{section:background}%


** Regular expressions: syntax and semantics
%\label{subsection:resyntaxsemantics}%


REs are defined with respect to a given alphabet. Formally, the following context-free
grammar defines RE syntax:
%
\[
e ::= \emptyset\,\mid\,\epsilon\,\mid\,a\,\mid\,e\,e\,\mid\,e+e\,\mid\,e^{\star}
\]
%
Meta-variable %$e$% will denote an arbitrary RE and %$a$% an
arbitrary alphabet symbol. As usual, all meta-variables can appear primed or subscripted.
In our Coq formalization, we represent alphabet symbols using type [ascii]. We let concatenation
of RE, strings and lists by juxtaposition. Notation %$|s|$%
denotes the size of an string %$s$%. Given a RE, we let its %\size$\,$% be defined by the following 
function:

%
\[
\begin{array}{lcl}
   \size(\emptyset) & = & 0 \\
   \size(\epsilon)  & = & 1 \\
   \size(a)         & = & 2 \\
   \size(e_1 + e_2) & = & 1 + \size(e_1) + \size(e_2)\\
   \size(e_1\,e_2)  & = & 1 + \size(e_1) + \size(e_2)\\
   \size(e ^\star)  & = & 1 + \size(e)
\end{array}
\]
%

Given a pair %$(e,s)$%, formed by a RE expression %$e$% and a string %$s$%, we define its complexity as
%$(\size(e),|s|)$%. 

Following common practice %\cite{Lopes2016,Ribeiro2017,Rathnayake2011}%, we adopt an inductive
characterization of RE membership semantics. We let judgment %$s \in \sembrackets{e}$% denote
that string $s$ is in the language denoted by RE $e$.

%
\begin{figure}[h]
	\[
	\begin{array}{cc}
	\infer[_{\{\Eps\}}]
	{\epsilon \in \sembrackets{\epsilon}}{} &
	\infer[_{\{\Chr\}}]
	{a \in \sembrackets{a}}{a \in \Sigma} \\ \\
	\infer[_{\{\Left\}}]
	{s \in \sembrackets{e + e'}}{s \in \sembrackets{e}} &
	\infer[_{\{\Right\}}]
	{s' \in \sembrackets{e + e'}}{s' \in \sembrackets{e'}} \\ \\
	\infer[_{\{\StarBase\}}]
	{\epsilon \in \sembrackets{e^\star}}{} &
	\infer[_{\{\StarRec\}}]
	{ss' \in \sembrackets{e^\star}}
	{s \in \sembrackets{e} & s' \in \sembrackets{e^\star}} \\ \\
	\multicolumn{2}{c}{
		\infer[_{\{\Catt\}}]
		{ss' \in \sembrackets{ee'}}
		{s \in \sembrackets{e} & s' \in \sembrackets{e'}}
	} \\
	\end{array}
	\]
	\centering
	\caption{RE inductive semantics.}
	\label{figure:resemantics}
\end{figure}
%

Rule %$\Eps$% states that the empty string (denoted by the %$\epsilon$%)
is in the language of RE %$\epsilon$%.

For any single character %$a$%, the singleton string [a] is in the language 
of RE %$a$%. Given membership proofs for REs %$e$% and %$e'$%, %$s \in \sembrackets{e}$% 
and %$s' \in\sembrackets{e'}$%, rule %$\Catt$% can be used to build a proof
for the concatenation of these REs.  Rule %\Left% (%\Right%) creates a membership proof
for %$e + e'$% from a proof for %$e$% (%$e'$%). Semantics for Kleene star
is built using the following well known equivalence of REs: %$e^\star
= \epsilon + e\,e^\star$%. 

We say that two REs are equivalent, written %$e\approx e'$%, if the following holds:
%
\[
\forall s. s\in \Sigma^\star \to s \in\sembrackets{e} \leftrightarrow s\in\sembrackets{e'} 
\]
%

** RE parsing and bit-coded parse trees

One way to represent parsing evidence is to build a tree that denotes
a RE membership proof. Following %\cite{Lasse2011,Frisch2004}%, we let
parse trees be terms whose type is its underlying RE. The following context-free 
grammar defines the syntax of parse trees, where we use a Haskell-like syntax for 
lists.
%
\begin{figure}[h]
   \[
      \begin{array}{lcl}
         t & \to & () \,\mid\, a \,\mid\, \texttt{inl}\:t  \,\mid\, \texttt{inr}\:t  \,\mid\, \langle t,\,t\rangle  \,\mid\, [\,]\,\mid\,t : ts
      \end{array}
   \]
   \caption{Parse trees for REs.}
   \label{figure:parsetreesyntax}
\end{figure}
%

Term %$()$% denotes the parse tree for $\epsilon$ and %$a$% the tree for a single character RE. 
Constructor%\texttt{inl}% (%\texttt{inr}%) tags parse trees for the left (right) operand in 
a union RE. A parse tree for the concatenation %$e\:e'$% is a pair formed by a tree for %$e$% and 
another for %$e'$%. A parse tree for %$e^\star$% is a list of trees for RE %$e$%. Such relationship 
between trees and RE are formalized by typing judgment %$\vdash t : e$%, which specifies that 
%$t$% is a parse tree for the RE %$e$%. The typing judgment is defined in Figure %\ref{figure:parsetreetyping}%.

%
\begin{figure}[h]
   \[ 
       \begin{array}{ccc}
         \infer{\vdash () : \epsilon}{} & \hspace{.5cm} & \infer{\vdash a : a}{}\\
         \\
         \infer{\vdash \texttt{inl }t : e + e'}{\vdash t : e}  & & 
         \infer{\vdash \texttt{inr }t : e + e'}{\vdash t : e'} \\ 
         \\
         \infer{\vdash \langle t_1, t_2 \rangle : e_1\:e_2}
               {\vdash t_1 : e_1 & \vdash t_2 : e_2}   & & 
         \infer{\vdash [\,] : e^\star}{} \\ \\
         \multicolumn{3}{c}{
           \infer{\vdash t : ts : e ^\star}
                 {\vdash t : e & \vdash ts : e ^\star}
         }
       \end{array}
   \]
   \caption{Parse tree typing relation.}
   \label{figure:parsetreetyping}
\end{figure}
%

For any parse tree %$t$%, we can produce its parsed string using function 
%\texttt{flatten}%, which is defined below:
%
\[
\begin{array}{lcl}
   \flatten\,() & = & \epsilon\\
   \flatten\,a  & = & a \\
   \flatten\,(\inl\:t) & = & \flatten\:t\\
   \flatten\,(\inr\:t) & = & \flatten\:t\\
   \flatten\,\langle t_1, t_2 \rangle & = & (\flatten\,t_1)(\flatten\,t_2)\\
   \flatten\,[\,] & = & \epsilon\\
   \flatten\,(t:ts) & = & (\flatten\,t)(\flatten\,ts)
\end{array}
\]                                                                                                                                
%
%
\begin{Example}
\label{example:parsetree}
Consider the RE $((ab)+c)^*$ and the string $abcab$, which is accepted by that RE. 
Here is shown the string's corresponding parse tree:

\begin{center}
\begin{tikzpicture}[tlabel/.style={font=\footnotesize}]
\node{$[\,]$}
child{
node{inl}
child{
node {$\langle,\rangle$}
child{node{a}}
child{node{b}}
}
}
child{
node{inr}
child{node {c}}
}
child{
node{inl}
child{
node {$\langle,\rangle$}
child{node{a}}
child{node{b}}
}
};
\end{tikzpicture}
\end{center}

\end{Example}
%
The next theorems relates parse trees and RE semantics.
The first one can be proved by an easy induction on the RE semantics derivation 
and the second by induction on the derivation of %$\vdash t : e$%.

%
\begin{Theorem}
   For all $s$ and $e$, if $s \in \sembrackets{e}$ then exists a tree $t$
   such that \texttt{flatten } $t$ = $s$ and $\vdash t : e$.
\end{Theorem}
\begin{proof}
  Induction on the derivation of $s \in \sembrackets{e}$.
\end{proof}
%

%
\begin{Theorem}
If $\vdash t : e$ then (\texttt{flatten }t)$\in\sembrackets{e}$. 
\end{Theorem}
\begin{proof}
   Induction on the derivation of $\vdash t : e$.
\end{proof}
%

Nielsen et. al. %\cite{Lasse2011}% proposed the
use of bit-marks to register which branch was chosen in a parse tree for union
operator, %$+$%, and to delimit different matches done by Kleene star expression.
Evidently, not all bit sequences correspond to valid parse trees. Ribeiro et. al. %\cite{Ribeiro2017}%
showed an inductively defined relation between valid bit-codes and RE, accordingly to the encoding
proposed by %\cite{Lasse2011}%. We let the judgement %$bs \rhd e$% denote that the sequence of bits
%$bs$% corresponds to a parse-tree for RE %$e$%.

%
\begin{figure}[h]
	\[
	\begin{array}{ccc}
	\infer{[\,] \rhd \epsilon}{} &
	\infer{[\,] \rhd a}{}  &
	\infer{0_b\, bs \rhd e + e'}{bs \rhd e} \\ \\
	\infer{1_b\,bs \rhd e + e'}{bs \rhd e'} &
	\infer{bs\,bs' \rhd e e'}{bs \rhd e & bs' \rhd e'} &
	\infer{ 1_b \rhd e^\star}{} \\ \\
	\multicolumn{3}{c}{
		\infer{0_b\,(bs\,bss) \rhd e^\star}{bs \rhd e & bss \rhd e^\star}
	}
	\end{array}
	\]
	\centering
	\caption{Typing relation for bit-codes.}
	\label{figure:typing-bitcodes}
\end{figure}
%
The empty string and single character RE are both represented by empty bit lists. Codes for RE %$ee'$% are
built by concatenating codes of %$e$% and $e'$. In RE union operator, %$+$%, the bit %$0_b$% marks that the
parse tree for %$e + e'$%  is built from %$e$%'s and bit %$1_b$% that it is built from %$e'$%'s. For the Kleene
star, we use bit %$1_b$% to denote the parse tree for the empty string and bit %$0_b$% to begin matchings of %$e$%
in a parse tree for %$e^\star$%.

The relation between a bit-code and its underlying parse tree can be defined using functions
%\code~% and %\decodee%, which generates a code for an input parse tree and parses a tree from a bit sequence, 
respectively. 

%
\[
\begin{array}{lcl}
   \code (() : \epsilon) & = & [\,]\\
   \code (a : a)         & = & [\,]\\
   \code (\inl\,t : e_1 + e_2) & = & 0_b\:\code(t : e_1)\\ 
   \code (\inr\,t : e_1 + e_2) & = & 1_b\:\code(t : e_2)\\
   \code (\langle t_1, t_2\rangle : e_1\,e_2) & = & \code (t_1 : e_1)\,\code(t_2 : e_2)\\
   \code ([\,] : e^\star) & = & 1_b\\
   \code ((t : ts) : e^\star) & = & \code (t : e)\:\code(ts : e^\star)\\ 
\end{array}
\]
%
Function %\code$\,$% has an imediate definition by recursion on the structure of a parse tree.
Note that the code generation is driven by input tree's type (i.e. its underlying RE).
In the definition of function %\decodee%, we use an auxiliar function, %\decodeo%, which 
threads the remaining bits in recursive calls.
%
\[
\begin{array}{lcl}
  \decodeo (bs : \epsilon) & = & ((), bs) \\
  \decodeo (bs : a)        & = & (a , bs) \\
  \decodeo (0_b\,bs : e_1 + e_2) & = & \leti\:(t,bs_1) = \decodeo (bs : e_1)\\
                                 &   & \iin\:(\inl\,t,bs_1)\\ 
  \decodeo (1_b\,bs : e_1 + e_2) & = & \leti\:(t,bs_2) = \decodeo (bs : e_2)\\
                                 &   & \iin\:(\inr\,t,bs_2)\\ 
  \decodeo (bs : e_1\,e_2) & = & \leti\:(t_1,bs_1) = \decodeo(bs : e_1) \\
                           &   & \,\,\,\,\,\,\,\,\,\,\,(t_2,bs_2) = \decodeo(bs_1 : e_2)\\
                           &   & \iin\:(\langle t_1,t_2\rangle, bs_2)\\
  \decodeo (1_b\,bs : e^\star) & = & ([\,],bs)\\
  \decodeo (0_b\,bs : e^\star) & = & \leti\:(t,bs) = \decodeo (bs : e)\\
                               &   & \,\,\,\,\,\,\,\,\,\,\,(ts,bs_1) = \decodeo(bs : e ^\star) \\ 
                               &   & \iin\: ((t : ts), bs_1)\\
  \\
  \decodee (bs : e) & = & \leti\:(t,bs_1) = \decodeo(bs : e)\\
                    &   & \iin\:\iif\:bs_1 = [\,]\:\tthen\:t\:\eelse\:\eerror \\
\end{array}
\]
%

For single character and empty string REs, its decoding consists in just building
the tree and leaving the input bit-coded untouched. We build a left tree (using %\inl%)
for %$e + e'$% if the code starts with bit %$0_b$%. A parse tree using constructor %\inr$\,$% is built
whenever we find bit %$1_b$% for a union RE. Building a tree for concatenation is done by
sequencing the processing of codes for left component of concatenation and starting the
processing of right component with the remaining bits from the processing of the left RE.
%
\begin{Example}
We present again the same RE and string we showed in Example \ref{example:parsetree},
denoted by $((ab) + c)^*$ and $abcab$, respectively. Note that the parse tree is also the same.
However, this time it contains its bit codes, which are $0_b0_b0_b1_b0_b0_b1_b$. The first, third and fifth
zeros in this sequence are separators and do not appear on the tree, as well as the last one
digit, which defines the end of the bit codes. Remaining three digits (two zeros and one one)
appear in each $\inl\,$ or $inr\,$ on the tree.

\begin{center}
\begin{tikzpicture}[tlabel/.style={font=\footnotesize}]
\node{$[\,]$}
child{
node{$0_b$:\inl}
child{
node {$\langle,\rangle$}
child{node{a}}
child{node{b}}
}
}
child{
node{$1_b$:\inr}
child{node {c}}
}
child{
node{$0_b$:\inl}
child{
node {$\langle,\rangle$}
child{node{a}}
child{node{b}}
}
};
\end{tikzpicture}
\end{center}

\end{Example}
%

The relation between codes and its correspondent parse trees are specified by the next
theorem.
%
\begin{Theorem}
  Let $t$ be a parse tree such that $\vdash t : e$, for some RE e. Then $(\code\: t\: e) \rhd e$ and
  $\decodee\: e\: (\code\: t\: e) = t$.
\end{Theorem}
\begin{proof}
  Induction on the derivation of $\vdash t : e$.
\end{proof}
%

** Dealing with problematic REs
%\label{subsection:problematic}%

A known problem in RE parsing is how to deal with the so-called problematic REs. A naive approach for 
parsing problematic REs can make the algorithm loop %\cite{Frisch2004}%. Medeiros et al. %\cite{Medeiros14}%
present a function which converts a problematic RE into a equivalent non-problematic one.

The conversion function relies on two auxiliar definitions: one for testing if a RE accepts the empty string and 
other to test if a RE is equivalent to %$\epsilon$%. We name such functions as %$\nullable\,$% and %\emptyy%, 
respectively.

%
\[
\begin{array}{lcl}
   \nullable(\emptyset) & = & \bot \\ 
   \nullable(\epsilon)  & = & \top \\
   \nullable(a)         & = & \bot \\ 
   \nullable(e_1 + e_2) & = & \nullable(e_1)\lor\nullable(e_2)\\
   \nullable(e_1\:e_2)  & = & \nullable(e_1)\land\nullable(e_2)\\
   \nullable(e ^\star)  & = & \top \\
   \\
   \emptyy(\emptyset)    & = & \bot \\ 
   \emptyy(\epsilon)     & = & \top \\
   \emptyy(a)            & = & \bot \\
   \emptyy(e_1 + e_2)    & = & \emptyy(e_1) \land \emptyy(e_2)\\
   \emptyy(e_1\:e_2)     & = & \emptyy(e_1) \land \emptyy(e_2)\\
   \emptyy(e ^\star)     & = & \emptyy(e)\\        
\end{array}
\]
%

Functions %\nullable$\,$% and %\emptyy$\,$% obeys the following correctness properties.

%
\begin{Lemma}
   \nullable($e$) = $\top$ if, and only if, $\epsilon\in\sembrackets{e}$.
\end{Lemma}
\begin{proof}$\,$\\
  $(\to)$ Induction over the structure of $e$. \\$(\leftarrow)$ Induction over the derivation of $\epsilon \in\sembrackets{e}$.
\end{proof}

\begin{Lemma}
   If \emptyy($e$) = $\top$ then $e \approx \epsilon$.
\end{Lemma}
\begin{proof}
   Induction over the structure of $e$.
\end{proof}
%  

Given these two predicates, Medeiros et.al. define two mutually recursive functions,
named %\fin$\,$% and %\fout%. The function %\fout$\,$% recurses over the structure of an input RE
searching for a problematic sub-expression and %\fin$\,$% rewrites the Kleene star subexpression
so that it became non-problematic and preserves the language of the original 
RE %\cite{Medeiros14}%. The definition of functions %\fin$\,$% and %\fout$\,$% are presented next.

%
\[
\begin{array}{lcl}
   \fout(e) & = & e,\,\texttt{if } e = \epsilon, e = \emptyset \texttt{ or } e = a\\
   \fout(e_1 + e_2) & = & \fout(e_1) + \fout(e_2) \\
   \fout(e_1\:e_2) & = & \fout(e_1)\:\fout(e_2)\\
   \fout(e^\star) & = & \left\{
        \begin{array}{ll}
           \fout(e)^\star & \texttt{if } \neg\,\nullable(e)\\
           \epsilon       & \texttt{if } \emptyy(e)\\
           \fin(e)^\star  & \texttt{otherwise}
        \end{array}
                          \right.
\end{array}
\]
%

%
\[
\begin{array}{lcl}
   \fin(e_1\:e_2) & = & \fin(e_1+e_2)\\
   \fin(e_1 + e_2) & = & \left\{
             \begin{array}{ll}
                \fin(e_2)  & \texttt{if }\emptyy(e_1) \land \nullable(e_2)\\
                \fout(e_2) & \texttt{if }\emptyy(e_1) \land \neg \nullable(e_2)\\
                \fin(e_1)  & \texttt{if }\nullable(e_1) \land \emptyy(e_2)\\
                \fout(e_1) & \texttt{if }\neg \nullable(e_1) \land \emptyy(e_2)\\
                \fout(e_1) + \fin(e_2) & \texttt{if }\neg \nullable(e_1) \land \neg\emptyy(e_2)\\
                \fin(e_1) + \fout(e_2) & \texttt{if }\neg \emptyy(e_1) \land \neg \nullable(e_2)\\
                \fin(e_1) + \fin(e_2) & \texttt{otherwise}
             \end{array}
                         \right. \\
   \fin(e^\star) & = & \left\{
             \begin{array}{ll}
               \fin(e) & \texttt{if }\nullable(e)\\
               \fout(e) & \texttt{otherwise}\\
             \end{array}
                       \right.
\end{array}
\]
%

The result of applying $\fout$ on a RE is producing an equivalent non-problematic one. This fact is expressed
by the following theorem. 

%
\begin{Theorem}
   If $\fout(e) = e'$ then $e \approx e'$ and $e'$ is a non-problematic RE.
\end{Theorem}
\begin{proof}
   Well-founded induction on the complexity of $(e,s)$, where $s$ is an arbitrary string, using
   several lemmas about RE equivalence and lemmas 1 and 2.
\end{proof}
%

This result is proved (informally) by Medeiros et. al. %\cite{Medeiros14}%. In order to formalize this result
in Coq, we needed to prove several theorems about RE equivalence. We postpone the discussion on some details
of our formalization to Section %\ref{section:formalization}%.

* Proposed semantics for RE parsing
%\label{section:semantics}%

In this section we present the definition of a big operational semantics for a VM for RE parsing.
The state of our VM is a pair formed by the current RE and the string being parsed. Each machine 
transition may produce, as a side effect, a bit-coded parse tree and the remaining string to be 
parsed. We denote our semantics by a judgement of the form %$\langle e, s \rangle \leadsto (bs,s_p,s_r)$%,
where %$e$% is current RE, %$s$% the string is the input string, %$bs$% is the produced bit-coded tree, %$s_p$% is
the parsed prefix of the input string and %$s_r$% is the yet to be parsed string.

%
\begin{figure}[h]
  \[
     \begin{array}{ccc}
        \infer[_{\{EpsVM\}}]{\langle \epsilon, s\rangle \leadsto ([\,],\epsilon,s)}{} & &
        \infer[_{\{ChrVM\}}]{\langle a, as\rangle\leadsto ([\,],a,s)}{} \\ \\
        \infer[_{\{LeftVM\}}]{\langle e_1 + e_2,s\rangle\leadsto (0_b\,b,s_p,s_r)}{\langle e_1, s\rangle \leadsto (b,s_p,s_r)} & &
        \infer[_{\{RightVM\}}]{\langle e_1 + e_2,s\rangle\leadsto (1_b\,b,s_p,s_r)}{\langle e_1, s\rangle \not \leadsto & 
                                                                \langle e_2, s\rangle \leadsto (b,s_p,s_r)} \\ \\
        \infer[_{\{CatVM\}}]{\langle e_1\:e_2,s\rangle\leadsto (b_1\,b_2,s_{p1},s_{p2},s_r)}
              {\begin{array}{c}
                  \langle e_1, s\rangle \leadsto (b_1,s_{p1},s_1) \\
                  \langle e_2, s_1\rangle \leadsto (b_2,s_{p2},s_r)
              \end{array}} & & 
        \infer[_{\{NilVM\}}]{\langle e^\star, s\rangle\leadsto (1_b,\epsilon,s)}{\langle e, s \rangle \not\leadsto}\\ \\

        \multicolumn{3}{c}{
           \infer[_{\{ConsVM\}}]{\langle e^\star, s\rangle\leadsto (b_1\,b_2,s_{p1}\,s_{p2},s_r)}
                 {\langle e, s \rangle \leadsto (b_1,s_{p1},s_1) & s_{p1} \neq \epsilon & 
                  \langle e^\star, s_1 \rangle \leadsto (b_2, s_{p2},s_r)}
        }
     \end{array}
  \]
  \caption{Operational semantics for RE parsing.}
  \label{figure:bigstepsemantics}
\end{figure}
%

The meaning of each semantics rules is as follows. Rule $EpsVM$ specifies that parsing $s$ using RE $\epsilon$ produces 
an empty list of bits and does not consume any symbol from $s$. Rule $ChrVM$ consumes the first symbol of the input string
if it matches the input RE. 
It is worth mention that our semantics impose an ordering for the choice operator. It first tries to parse the input 
using the left choice operand. The right operand is only executed by the VM when parsing the input string using the left 
one fails (we represent parsing failure for an RE %$e$% and string %$s$% as %$\langle e, s\rangle\not\leadsto$%). Rules $LeftVM$ and 
$RightVM$ specifies how the semantics executes an RE %$e + e'$%. Note that, as a result, we append a bit $0_b$ when we successfully 
parse the input using the left choice operand and the bit %$1_b$% for a parsing using the right operand. Rule $CatVM$ defines 
how a concatenation %$e_1\,e_2$% is executed by the semantics: first, the input is parsed using the RE %$e_1$% and the remaining 
string is used as input to execute %$e_2$%. The bit-coded tree for the %$e_1\,e_2$% is just the concatenation of the produced 
codes for $e_1$ and $e_2$. Rules %$NilVM$% and %$ConsVM$% deal with Kleene star REs. The rule %$NilVM$% is only applicable when
is not possible to parse the input using the RE %$e$% in %$e^\star$%. Rule %$ConsVM$% can be used whenever we can parse the
input using %$e$% and the parsed prefix is not an empty string. The remaining string (%$s_1$%) of %$e$%'s parsing is used as
input for the next iteration of RE %$e^\star$% parsing. 

Evidently, the proposed semantics is sound and complete w.r.t. standard RE semantics.

%
\begin{Theorem}[Soundness]
  If $\langle e, s \rangle \leadsto (bs,s_p,s_r)$ then $s = s_p\,s_r$ and $s_p\in\sembrackets{e}$.
\end{Theorem}
\begin{proof}
  Well-founded induction on the complexity of $(e,s)$.
\end{proof}

\begin{Theorem}[Completeness]
  If $s_p\in\sembrackets{e}$ then for all $s_r$ we have that exists $bs$, s.t. $\langle e, s_p\,s_r \rangle \leadsto (bs,s_p,s_r)$.
\end{Theorem}
\begin{proof}
  Well-founded induction on the complexity of $(e,s)$.
\end{proof}

\begin{Theorem}[Parsing result soundness]
  If $\langle e, s \rangle \leadsto (bs,s_p,s_r)$ then: 1) $bs \rhd e$; 2) $\flatten(\decodee(bs : e)) = s_p$; and 3)
  $\code(\decodee(bs : e) : e) = bs$. 
\end{Theorem}
\begin{proof}
  Well-founded induction on the complexity of $(e,s)$ using Theorem 3.
\end{proof}
%

* Coq formalization
%\label{section:formalization}%

In this section we describe some details of our Coq formalization for the proposed VM for RE parsing.
FALAR DA SEMÂNTICAS, BIT-CODING e PARSE TREES. EQUIVALÊNCIA DE REs. FORMALIZAÇÃO DO FOUT. INTERPRETADOR
DA VM.



* Related work
  %\label{section:related}%

Ierusalimschy %\cite{Ierusalimschy2009}% proposed the use of Parsing Expression Grammars (PEGs) as a basis
for pattern matching. He argued that pure REs is a weak formalism for pattern-matching tasks:
many interesting patterns either are difficult to to describe or cannot be described by REs. He also said
that the inherent non-determinism of REs does not fit the need to capture specific parts of a match. Following
this proposal, he presented LPEG, a pattern-matching tool based on PEGs for the Lua language. He
argued that LPEG unifies the ease of use of pattern-matching tools with the full expressive power of PEGs.
He also presented a parsing machine (PM) that allows an implementation of PEGs for pattern matching.
In %\cite{Medeiros2008}%, Medeiros et. al. presents informal correctness proofs of LPEG PM.
While such proofs represent a important step towards the correctness of LPEG, there is no guarantee that LPEG
implementation follows its specification.

In %\cite{Rathnayake2011}%, Rathnayake and Thielecke formalized a VM implementation for RE matching using
operational semantics. Specifically, they derived a series of abstract machines, moving from the abstract
definition of matching to realistic machines. First, a continuation is added to the operational semantics
to describe what remains to be matched after the current expression. Next, they represented the expression
as a data structure using pointers, which enables redundant searches to be eliminated via testing for pointer
equality. Although their work has some similarities with ours (a VM-based parsing of REs), they did not present
any evidence or proofs that their VM is correct.

Fischer, Huch and Wilke %\cite{Fischer2010}% developed a Haskell program for matching REs. The program is purely
functional and it is overloaded over arbitrary semirings, which solves the matching problem and supports other
applications like computing leftmost longest matchings or the number of matchings. Their program can also be used
for parsing every context-free language by taking advantage of laziness. Their developed program is based on an
old technique to turn REs into finite automata, which makes it efficient compared to other similar approaches.
One advantage of their implementation over our proposal is that their approach works with context-free languages,
not only with REs purely. However, they did not present any correctness proofs of their Haskell code.

Cox %\cite{Cox2009}% said that viewing RE matching as executing a special machine makes it possible to add new
features just by the inclusion of new machine instructions. He presented two different ways to implement
a VM that executes a RE that has been compiled into  byte-codes: a recursive and a non-recursive
backtracking implementation, both in C programming language. Cox's work on VM-based RE parsing is poorly specified:
both the VM semantics and the RE compilation process are described only informally
and no correctness guarantees is even mentioned.

Frisch and Cardelli %\cite{Frisch2004}% studied the theoretical problem of matching a flat sequence against a type (RE): the
result of the process is a structured value of a given type. Their contributions were in noticing that: (1) A disambiguated
result of parsing can be presented as a data structure that does not contain ambiguities. (2) There are problematic cases in
parsing values of star types that need to be disambiguated. (3) The disambiguation strategy used in XDuce and CDuce (two
XML-oriented functional languages) pattern matching can be characterized mathematically by what they call greedy RE matching.
(4) There is a linear time algorithm for the greedy matching. Their approach is different since they want to axiomatize abstractly
the disambiguation policy, without providing an explicit matching algorithm. They identify three notions of problematic words, REs,
and values (which represent the ways to match words), relate these three notions, and propose matching algorithms to deal with the
problematic case.

Ribeiro and Du Bois %\cite{Ribeiro2017}% described the formalization of a RE parsing algorithm that produces a bit representation
of its parse tree in the dependently typed language Agda. The algorithm computes bit-codes using Brzozowski derivatives and
they proved that the produced codes are equivalent to parse trees ensuring soundness and completeness with respect to an
inductive RE semantics. They included the certified algorithm in a tool developed by themselves, named verigrep, for RE-based
search in the style of GNU grep. While the authors provide formal proofs, their tool show a bad performance when compared with
other approaches to RE parsing. Besides, they did not prove that their algorithm follows some disambiguation policy, like POSIX
or greedy.

Nielsen and Henglein %\cite{Lasse2011}% showed how to generate a compact bit-coded representation of a parse tree for a
given RE efficiently, without explicitly constructing the parse tree first, by simplifying the DFA-based parsing algorithm of
Dubé and Feeley %\cite{Dube2000}% to emit a bit representation without explicitly materializing the parse tree itself.
They also showed that Frisch and Cardelli’s greedy RE parsing algorithm %\cite{Frisch2004}% can be straightforwardly modified to
produce bit codings directly. They implemented both solutions as well as a backtracking parser and performed benchmark experiments
to measure their performance. They argued that bit codings are interesting in their own right since they are typically not
only smaller than the parse tree, but also smaller than the string being parsed and can be combined with other techniques for
improved text compression. As others related works, the authors did not present a formal verification of their implementations.

An algorithm for POSIX RE parsing is described in %\cite{Sulzmann14}%. The main idea of the article is to adapt
derivative parsing to construct parse trees incrementally to solve both matching and submatching for REs. In order to improve the
efficiency of the proposed algorithm, Sulzmann et al. use a bit encoded representation of RE parse trees. Textual proofs of
correctness of the proposed algorithm are presented in an appendix.

* Experimental results
%\label{section:experiments}%


* Conclusion
%\label{section:conclusion}%

In this work, we presented a big-step operational semantics for a virtual machine for RE parsing. 
Our semantics produces, as parsing evidence, bit-codes which can be used to characterize which
disambiguation strategy is followed by the semantics. In order to avoid the well-known problems with 
problematic REs, we use an algorithm that converts a problematic RE into an equivalent non-problematic one.
All theoretical results reported in this paper are intregrally verified using Coq proof assistant.
From our formalization, we extract a Haskell implementation of our algorithm and used it to build 
a tool for RE parsing.
*)