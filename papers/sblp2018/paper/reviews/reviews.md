----------------------- REVIEW 1 ---------------------
PAPER: 4
TITLE: Towards certified virtual machine-based regular expression parsing
AUTHORS: Thales Delfino and Rodrigo Ribeiro

Overall evaluation: 0 (borderline paper)

----------- Overall evaluation -----------
This paper describes interesting and promising work on the reduction semantics of regular expression parsing.
My comments are in the attached PDF but, in summary, the paper as it is needs some important rewriting to
make clear what appears to be (as I understand it) the main aspects of their work:
(i) the choice of a VM-based approach,
(ii) the use of reduction semantics and
(iii) the properties of the automated testing.
I believe that much of the implementation details, that are very important indeed, could be left to the technical report
(or something like a Jupyter notebook) and open room for much needed higher-level (than code) explanations.
Due to these clarifications and that, perhaps, publishing it now could be a bit premature (perhaps with some prototype-level Coq coding?), I will not champion it. I certainly suggest it to be accepted if room.


----------------------- REVIEW 2 ---------------------
PAPER: 4
TITLE: Towards certified virtual machine-based regular expression parsing
AUTHORS: Thales Delfino and Rodrigo Ribeiro

Overall evaluation: 0 (borderline paper)

----------- Overall evaluation -----------
The text presents a virtual machine for parsing regular languages,
based on a small-step semantics for regular expressions. The machine
is tested with the help of test tool (QuickCheck) and there are "proof
sketches" for its correctness. It is well-written and quite clear.

As it stands, the text is a nice exercise in formal languages, but
I am not sure it has enough material to deserve a publication in SBLP.
As the main contribution would be a "certified" machine, I think a
really formal proof (e.g., in Coq), or at least some concrete work in
that direction, would make this work much more valuable. Simply "proof
sketches" does not seem enough for a work where the main topic are
the proofs themselves, as we have no guaranties these sketches can lead
to real proofs. In this case in particular, I suspect they cannot.

A known problem in interpreters for regular-expressions is what the
paper calls "problematic REs", that is, a regular expression that
contains a Kleene closure over a nullable expression. As far as I could
see, the presented implementation would loop forever in failed
matches against problematic REs. For instance, a match of "b" against
the pattern "(a?)*c" would try infinite ways of matching "(a?)*" against
the empty string before 'b', and the program would never be able to
conclude that the resulting list is empty.

When I saw this problem in the algorithm, I could not understand why the
exhaustive tests did not detect the problem. Then I found the explanation:

  For simplicity and brevity, we only generate REs that do not
  contain sub-REs of the form e? , where e is nullable. All results
  can be extended to non-problematic REs in the style of Frisch et.
  al [13].

Probably the text meant "problematic REs" instead of "non-problematic
REs".  Nevertheless, Theorem 3 does not hold for all REs, as its
hypothesis states, but only for non-problematic ones.

Another problem in the algorithm is its time complexity. The paper
says the algorithm was inspired on Thompson's construction. (I could
not see the relationship between the two approaches, but that is not
relevant here.) However, the paper fails to describe a key property of
the Thompson's construction: Although it constructs a non-deterministic
automata, it runs the result as a deterministic one, and therefore it
runs in linear time. (Thompson's algorithm represents its [deterministic]
state as a list of [non-deterministic] states from the resulting NFA.)
Unlike Thompson's construction, however, the presented algorithm seems
to have exponential complexity in its worst case.


Follows some remarks about the text:

* The description of the type Ctx is confusing. First, the paper
says (and the name implies) that the type Ctx implements contexts,
when in fact contexts are actually lists of Ctx (as the paper
explains later).

* In Theorem 3, it would be simpler to state directly that

  <B, e, [], [], s>  -*-> <F, e', [], b, []>

instead of using the more general format <E, e', {}, b, []> and demanding
that it is an accepting configuration.

* In Figure 4, all "preconditions" are in fact definitions. Maybe
it would be simpler to expand that definitions instead of using
these "preconditions"? For instance, instead of

   c' = e E[] : c
------------------------------
<F,e,E[]e':c,b,s> -> <B,e',c',b,s>

one could write directly

<F,e,E[]e':c,b,s> -> <B,e',e E[] : c,b,s>

* In function 'accept', it would be more idiomatic to return Maybe Code,
instead of a pair (Bool, Code).


----------------------- REVIEW 3 ---------------------
PAPER: 4
TITLE: Towards certified virtual machine-based regular expression parsing
AUTHORS: Thales Delfino and Rodrigo Ribeiro

Overall evaluation: 1 (weak accept)

----------- Overall evaluation -----------
The paper presents a virtual machine (VM) for parsing regular expressions (REs) whose conception is based on Thompson's non-deterministic finite automata. The presentation of the VM is in the form of a small-step operational semantics between configurations that keep track of the context in which the current RE is being evaluated and produce bit-codes denoting parse trees. Contexts are represented by a zipper-like structure containing the list of RE evaluation contexts which were traversed to reach the current RE. A prototype implementation of the VM is developed in Haskell and tested with QuickCheck. The datatype that implements evaluation contexts is obtained from that for REs by applying derivatives.

Although presenting a relatively small constribution, I find the paper very interesting, with an approapriate presentation of background material and related work. The document is well-written and clear.

The design of the VM seems the right one. It would be helpful if you can give some explanation about the correspondence between the rules of the VM and the automata. If I am understanding correctly, it seems that many of the rules correspond to the extra epsilon transitions that are added in the construction of the NFA; a rule for those cases does not advance on the string and simply needs to perform the neccesary adjustments on the context and the produced bit-code before entering or after exiting a sub-automata N(e).

- Specific comments

page.1
LPEG [16] define_s_ a VM
a_n_ evidence

page.2, sect 2.2
is is

page.3
In the definition of code (List ts) (Star e) = 0_b : codeList ts e, is it correct to always put 0_b at the front? This means that the bit-code for a Kleene star is always of the form 0_b : <...> independently it corresponds to an empty or non-empty list of trees. In case a 0_b needs to be always at the front of the bit-code for a star, then it should be consumed by the star case of function dec, i.e. this case should be defined this way:
dec (Star e) (0_b : bs) = do ....

page.4
in the introduction of configurations: "(starting by S)" should be a B instead of S
in Theorem 3 (twice): should be direction F instead of E in the final configuration

page.5
equations of next deal*s* with

page.6
closure of _the_ semantics
parsed by the RE -> parser by a RE

Function accept could return something of type Maybe Code instead of a pair of type (Bool,Code)

page.8
Reference [21] is incomplete, is it a technical report, a thesis?
Reference [27] is incomplete, the proceedings of FLOPS 2014 appear in LNCS.