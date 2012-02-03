% Motivation
% Péter Diviánszky
% 2011. 05. 03.

\begin{code}
module Motivation_a where
\end{code}


What is Agda?
=============

Agda is a programming language which is targeted to produce
safe and fast code.


How Agda Helps Safe Code
========================

Phases in which errors can be found during program development:

-   specification
-   implementation
-   testing
-   after deployment

The sooner the cheaper!

--------------

With Agda, it is possible to find the vast majority of errors in the specification and in the implementation phase.

|In Agda, we don't try to prove that the implementation is safe.
|We try to implement the specification instead.


How Agda Helps Fast Code
========================

These activities can be done either in compile-time (once) or in runtime (many times):

-   Lexical and syntactic analysis, scope checking (during runtime for interpreted languages)
-   Type checking
-   Exceptions: Array boundary check, null-pointer check, divide-by-zero exception, ...
-   Termination check (cycle-in-spine and deadlock check in Haskell runtime)
-   Sanity check (for example: Is the input already sorted?)
-   Garbage collection, stack overflow check, memory and time limit checks, ...

Better to do them at compile-time!

------------

In Agda, it is possible to do all but the last ones at compile-time.


Most compilers are checking invariants on implementations and try to
deduce information for optimization.

In Agda we write specification, implementation and consistency proofs at the same time.  
All these information are available for the compiler!


About
=====

Our goal is to give a practical, self contained Agda introduction.

----------------

Pressing key 'a' on the pages switch between slide and normal mode.  
Navigation is possible with left and right arrows.  
In slide mode the remarks are not visible!

The developers are Péter Diviánszky and Ambrus Kaposi.



