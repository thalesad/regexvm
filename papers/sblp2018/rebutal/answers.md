Reviewer 1
==========

1. It is very cool that your approach is fully formal and fully available for experimentation. I managed to clone and execute your code, after upgrading stack.

*Answer:* Thanks! We believe that is very important to make the work reproducible.

2. The main problem for me is that I am not convinced on _why_ I should use your technique and tooling.  Would it be because your tests gave us some confidence that it implements the NFA_epsilon semantics of RE?

*Answer:* Our long term goal is to investigate the suitability of using VMs for RE parsing. In order to reach such objective, we think that
we should provide a correct semantics and our paper reports on the design of such VM and the use of property based testing to check if our
definitions make sense. Currently, we are working towards a fully verified implementation of our semantics in Coq proof assistant. We add
a paragraph in the introduction about the current status of the mechanization.

3. The section on the properties QuickCheck checks for _must be_ increased with an in depth description, with code if you must, on why correctness is enforced by your tests. Give more examples and details on how the verification process functions.

*Answer:* We have used a short description of tests due to space reasons. We will expand the description of the test suite on the technical report.

4. If the use of reduction contexts is a key point in your approach, it should be better explained.

*Answer:*

5. What about efficiency with respect to other implementations? You mentioned PEG but you treat only RE, correct? (PEG is more expressive than RE, it covers some CFG and some CSG as well.)

*Answer:* Currently we are interested on the correctness of our VM semantics. We are aware that our semantics didn't allow for an efficient implementation of parsing.
After having fully mechanized proofs, we intend to adapt the ideas of [1] to the context of RE matching in order to achieve better performance.

6. Isn’t your approach greedy as well? This is what you say in your GitHub.

*Answer:* There is a subtle difference between how PEG and RE interprets the Kleene star operator. The semantics of RE Kleene star can be seen as a
non-deterministic loop, while PEG's isn't. PEG star operator will match *all* the possible occurrences of the described pattern.
For instance, the RE a^\star a matches the string "aaa" correctly, since the a^\star operator should non-deterministically stop after processing the
second 'a' leting the last one to be consumed by the RE a. Observe that, the same expression executed using PEG semantics will never succeed,
since it will try to consume all occurrences of character "a" using the star operator then it will fail by trying to match the empty string with the expression 'a'.

7. Why? Only VM based algorithm can do that?

*Answer:* There are other approaches for building evidence for parsing as bit-strings. We mention (on related works section) the works of Frisch2004 and Sulzmann on building
such codes as parsing results.

8. which we conjecture is correct.

*Answer:* We are working in the verification of this function.

9. Use \mathit around words in math mode.

*Answer:* Ok, fixed.

10. What bit-coded parse trees are, what are they for and why are they important?

*Answer:* We added the following text in the introduction, to explain why bit-coded
representation of parse-trees are relevant.

As pointed by~\cite{Lasse2011}, bit-codes are useful because they
are not only smaller than the parse tree, but also smaller than the string being parsed and they can be combined with methods
for text compression.

11. An example would be _very_ useful here.

*Answer:* We omit examples for all definition from the paper for space reasons. We modify the technical report to include
examples of relevant definitions. The report is available at:

REPORT LINK HERE

12. encoding?

*Answer:* Ok, fixed.

13. What does e’ mean?

*Answer:* It represents an arbirary RE. We added the following sentence in section 2.1:

As usual, meta-variable $e$ will denote an arbitrary RE and it can appear primed or subscripted.

14. Where? Fig. 1?

*Answer:* We added references to the relevant figures. Thanks!

15. This is actually a scheme of rules, \forall a \in Sigma, correct?

*Answer:* Yes. The variable 'a' denotes an arbitrary alphabet symbol. We added the following sentence in section 2.1

Meta-variable $e$ will denote an arbitrary RE and $a$ an arbitrary alphabet symbol. As usual, all meta-variables can appear primed or subscripted.

16. This section needs to be expanded a lot! Isn’t it the major difference between your approach and the state-of-the-art?

*Answer:* We agree that the test suite description is suscint, but it isn't the major contribution of our work. We believe
that the small-step semantics is our main contribution. The usage of property based testing is just a way to check if
the designed semantics rules are appropriate. We expand the description of the test suit in the technical report available at:

REPORT LINK HERE.

17. This appears to be a good Soft eng. metric but is not really related with correctness with respect to NFA_e semantics, correct?

*Answer:* Yes, it isn't. Our test suite check if the proposed semantics is sound and complete with respect to a standard RE semantics.


18. Move to conclusion.

*Answer:* We removed the last paragraph of section 4.

19. I have not been able to grasp that!

*Answer:*


Reviewer 2
==========

1.  As it stands, the text is a nice exercise in formal languages, but I am not sure it has enough material to deserve a publication in SBLP. As the main contribution would be a "certified" machine, I think a really formal proof (e.g., in Coq), or at least some concrete work in that direction, would make this work much more valuable. Simply "proof sketches" does not seem enough for a work where the main topic are the proofs themselves, as we have no guaranties these sketches can lead to real proofs. In this case in particular, I suspect they cannot.

*Answer:* Currently, we have a verified interpreter of the semantics in Coq proof assistant and we are working towards the
mechanization of the equivalence proof between the small step semantics and the traditional (big-step) RE inductive semantics.
We included a sentence about this formalization and added it to project's on-line repository.

2. A known problem in interpreters for regular-expressions is what the paper calls "problematic REs", that is, a regular expression that contains a Kleene closure over a nullable expression. As far as I could see, the presented implementation would loop forever in failed matches against problematic REs. For instance, a match of "b" against the pattern "(a?)*c" would try infinite ways of matching "(a?)*" against the empty string before 'b', and the program would never be able to conclude that the resulting list is empty. When I saw this problem in the algorithm, I could not understand why the exhaustive tests did not detect the problem. Then I found the explanation:

  For simplicity and brevity, we only generate REs that do not
  contain sub-REs of the form e? , where e is nullable. All results
  can be extended to non-problematic REs in the style of Frisch et.
  al [13].

Probably the text meant "problematic REs" instead of "non-problematic
REs".  Nevertheless, Theorem 3 does not hold for all REs, as its
hypothesis states, but only for non-problematic ones.

*Answer:* We will rewrite the text to clearly specify that the current version deals only with non-problematic REs. In our view, dealing with
problematic REs will only clutter the presentation without adding any new insight. We added the following paragraph at the end of section 2.1:

We say that a RE $e$ is \emph{problematic}
if $e = e'^\star$ and $\epsilon \in \sembrackets{e'}$~\cite{Frisch2004}.
In this work, we limit our attention to non-problematic RE's. Our results
can be extended to problematic REs without providing any
new insight~\cite{Lasse2011,Frisch2004}.

3. Another problem in the algorithm is its time complexity. The paper says the algorithm was inspired on Thompson's construction. (I could not see the relationship between the two approaches, but that is not relevant here.) However, the paper fails to describe a key property of the Thompson's construction: Although it constructs a non-deterministic automata, it runs the result as a deterministic one, and therefore it runs in linear time. (Thompson's algorithm represents its [deterministic] state as a list of [non-deterministic] states from the resulting NFA.) Unlike Thompson's construction, however, the presented algorithm seems to have exponential complexity in its worst case.

*Answer:* We are aware of the time complexity of the algorithm and we intend to investigate how to improve its efficiency after we have formally verified proofs.
A direction we want to investigate is to adapt the works on the optimization of abstract abstract machines [1] to our VM.

4. The description of the type Ctx is confusing. First, the paper says (and the name implies) that the type Ctx implements contexts, when in fact contexts are actually lists of Ctx (as the paper explains later).

*Answer:* We rename type Ctx to Hole in order to avoid such confusion.

5. In Theorem 3, it would be simpler to state directly that

  <B, e, [], [], s>  -*-> <F, e', [], b, []>

instead of using the more general format <E, e', {}, b, []> and demanding
that it is an accepting configuration.

*Answer:* This was a typesetting error. The correct would be as you stated. Thanks for pointing that.


Reviewer 3
==========


1. LPEG [16] define_s_ a VM a_n_ evidence

*Answer:* Fixed. Thanks!

2. is is

*Answer:* Fixed. Thanks!

3. In the definition of code (List ts) (Star e) = 0_b : codeList ts e, is it correct to always put 0_b at the front? This means that the bit-code for a Kleene star is always of the form 0_b : <...> independently it corresponds to an empty or non-empty list of trees. In case a 0_b needs to be always at the front of the bit-code for a star, then it should be consumed by the star case of function dec, i.e. this case should be defined this way: dec (Star e) (0_b : bs) = do ....

*Answer:* The equation for code function in star case is wrong! Probably a error during the paper writing.
Thanks for pointing that! In our source code, we have the following equation:

code (TList ts) (Star e) = codeList ts e

Which has the correct behaviour.

4. in the introduction of configurations: "(starting by S)" should be a B instead of S

*Answer:* Fixed. Thanks!


5. in Theorem 3 (twice): should be direction F instead of E in the final configuration


*Answer:* Fixed. Thanks!


6. equations of next deal*s* with

*Answer:* Fixed. Thanks!

7. closure of _the_ semantics

*Answer:* Fixed. Thanks!

9. Reference [21] is incomplete, is it a technical report, a thesis?

*Answer:* Fixed. We use the citation to the LNCS publication.

10. the proceedings of FLOPS 2014 appear in LNCS.

*Answer:* Fixed. Thanks!


References
==========

@inproceedings{Johnson:2013:OAA:2500365.2500604,
 author = {Johnson, J. Ian and Labich, Nicholas and Might, Matthew and Van Horn, David},
 title = {Optimizing Abstract Abstract Machines},
 booktitle = {Proceedings of the 18th ACM SIGPLAN International Conference on Functional Programming},
 series = {ICFP '13},
 year = {2013},
 isbn = {978-1-4503-2326-0},
 location = {Boston, Massachusetts, USA},
 pages = {443--454},
 numpages = {12},
 url = {http://doi.acm.org/10.1145/2500365.2500604},
 doi = {10.1145/2500365.2500604},
 acmid = {2500604},
 publisher = {ACM},
 address = {New York, NY, USA},
 keywords = {abstract interpretation, abstract machines},
}








