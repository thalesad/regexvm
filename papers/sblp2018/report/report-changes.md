Report changes
==============

1. Merge the changes done in SBLP paper in the report in order to make them consistent.
2. Include examples for:
   a) Thompson NFA construction: Show the automata constructed for some RE.
   b) Parse trees and bit coding. Maybe we could include some material from the dissertation proposal.
3. Explain how the contexts are used in semantics.
   a) We need to show the relation of semantics rules and the transitions on Thompson NFA.
   Basically, show that starting rules correpond to transitions entering some sub-automata and
   finishing rules to transitions exiting a sub-automata. Would be nice that if show the semantics
   execution side-by-side with the corresponding partial Thompson automata.
   b) We should use the example used in item 1a.
4. Describe the test suite.
   a) We need a proper introduction to Quickcheck. Such introduction should describe how the library
   can be used to test simple functions. There are a plenty of tutorials that can be used to get
   simple examples to ilustrate the usage of Quicheck.
   b) We need to describe the test case generators. Here, I suggest that you put the complete specification
   of how RE and strings are generated and explain them.
   c) We need to describe the properties tested. The last point is to use our Haskell implementation of the
   properties tested to describe them properly.
5. Coq partial formalization. I believe that is necessary to explain the certified interpreter for the proposed
   semantics. Leave the writing of this part to me.
