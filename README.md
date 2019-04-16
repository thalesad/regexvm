Certified virtual machine based regular expression parsing.
==================

Introduction
--------


This project aims to develop a fully verified and efficient tool for regular expression parsing 
using an operational semantics inspired by virtual machines for lambda-calculus like SECD and Krivine 
machines.

The current repository contains the complete Coq formalization of the algorithm and a Haskell prototype
which was developed in early versions of the project. 

Coq formalization 
---------------------

Our formalization has the following folder structure:

1. Folder Utils: Functions and theorems over strings and lists that aren't part of Coq standard library.
2. Folder Tactics: Libraries of tactics developed in Software Foundations and Certified Programming with 
                   dependent types.
3. Folder Syntax: Regular expression syntax, semantics, parse trees, bit-coded parse trees and the 
                  formalization of a function to convert a problematic regular expression into an 
                  equivalent non-problematic.
4. Folder Semantics: Formalization of the virtual machine and its interpreter.
5. Folder Tool: Extraction and Haskell code infrastructure to build the certified regular expression 
                parsing tool using the formalized algorithm.
                
The development was verified using Coq version 8.9.0 and it can be compiled using the makefile inside folder 
coqformalization.


Executing the tool produced and running the benchmarks
-------------

The regular expression parsing tool was developed using Haskell. In order to manage Haskell libraries and its 
build process, we use [Haskell stack tool](https://docs.haskellstack.org/en/stable/README/) version 1.9.3. 
The Haskell stack project is inside the folder coqformalization/Tool/regex-vm. 
             
Having it installed, you will need to set-up the environment. For this, execute:

     stack setup

This command will install all necessary libraries and the GHC compiler, if needed.
With a proper environment configured, execute:

     stack build

to build the executables for the parsing tool and the benchmark suite. To execute the tool, just run:

     stack exec regex-vm-exe

The benchmark used can be execute by the following command 

    stack exec regex-vm-bench
    
In order to produce the graphs presented in the paper, you will need [GnuPlot](http://www.gnuplot.info).


Haskell prototype of the SBLP 2018 paper
---------------------------------------

The code for the Haskell prototype for the SBLP 2018 is available at folder 
haskellprototype.
