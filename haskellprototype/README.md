An operational semantics for greedy regular expression parsing
==================

This is a Haskell prototype of an operational semantics for greedy regular 
expression parsing.

Test suite
---------

We use Quickcheck, to generate random regular expressions and 
random strings that can be parsed by them, and compare the result of 
our semantics with the accept function present in 
"A play on regular expressions" by  Fisher et. al, which can be seem 
as an implementation of the standard big-step semantics for 
regular expressions.


Executing the test suite
----------------
 
To execute the test suite you will need the [Haskell stack tool](https://docs.haskellstack.org/en/stable/README/).
Having it installed, you will need to set-up the environment. For this, execute:

     stack setup
     
This command will install all necessary libraries and the GHC compiler, if needed.
With a proper environment configured, just execute:


     stack test 
     
to run the test suite. Currently, the test suite generates 10.000 random regular expressions
and strings accepted by them. To change this number, just modify the file test/Spec.hs.

Building the paper
---------------

The paper "Towards certified virtual-machine based regular expression parsing" is a literate 
Haskell file that can be pre-processed using [lhs2TeX](https://hackage.haskell.org/package/lhs2tex). 
A makefile that builds the paper is avaliable at folder papers/sblp2018/paper. 


Technical report
------------------

A technical report containing all proofs omitted from the paper is avaliable at folder  papers/sblp2018/report 
and it can be built using the makefile in the report directory.


Code coverage results
-------------

The coverage of our test suite can be produced using the command 

     stack test --coverage

which will generate a html report.

Coq formalization
----------------

We have a partial formalization of the proposed semantics in Coq proof assistant. The code is part of a bigger
goal of building a complete certified tool for regular expression parsing in Coq. The current status of our 
formalization is avaliable at folder coq/regex/VM.
