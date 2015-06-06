% Motivation
% Ambrus Kaposi, Péter Diviánszky
% 2012. 02. 13., 2013. 01.

<!--
\begin{code}
module Motivation where
\end{code}
-->

About this tutorial
==================

Goals

- Show what Agda is good for
- Teach Agda syntax and semantics
- Teach Agda programming skills

Features

- Slides: 1/3 examples, 1/3 explanation, 1/3 exercises
- Only (part of) secondary school mathematics is required

[*More about this tutorial*](About.html)


What is Agda good for?
=====================

**Utilize the capacity of the computers in a reliable way.**

Targets:

- Joining programming and mathematics
- Formal definitions, theorems, proofs, and algorithms


Benefits of programming in Agda
===============================

-   **Elimination of errors**

    -   no runtime errors  
        Inevitable errors like I/O errors are handled, others are excluded by design.
    -   no non-productive infinite loops

-   **Machine-checked documentation**  

    -   any functional properties can be formalized and proved -- proof checking is automatic
    -   distinction between finite and infinite data like lists vs. streams
    -   invariant properties of data like sorted lists and balanced trees can be maintained
    -   function properties like commutativity, associativity can be maintained

-   **Exact interfaces**  

    Formal specification can be given with the help of exact mathematical concepts like 
    groups, rings, lattices, categories, and so on.

-   **Safe optimization**

    -   runtime checks like array bounds checks are eliminated
    -   defensive coding (generous on input, strict on output) is unnecessary -- there is no overhead of it
    -   safe optimization on special input like associative input function of a higher-order function

-   **High-level programming**

    -   programming with types as data (generic programming, universes)  
        Types may depend on values in run time and still checked in compile time.
    -   reflection
    -   previously unseen range of embedded domain-specific languages
        can be defined with arbitrary precision


Benefits of creating formal systems in Agda
==============================

Definitions

-   Classical, constructive, and modal logical connectives can be defined.

Theorems

-   One can quantify over elements, properties, properties of properties etc.  
    (Agda has the strength of an infinite-order logic.)

Proofs

-   Automatic simplification of expressions gives the
    automatic part of proofs.  
    This way algorithms can be used in proofs.
-   Automatic proof checking.

Additional features

-   Inferred terms, implicit arguments.
-   Holes, interactive development.
-   Unicode characters, mixfix operators.



<!-- comment
| Eliminating errors from programming
| ===================================
| 
| Method               Example
| -------------------  ----------------------------------------
| run-time monitoring  `Exception in thread "main" java.lang.ArrayIndexOutOfBoundsException`
| testing              `quickCheck ((\s → s == s) : List Char → Bool)`
| model checking       NuSMV
|                      `state : {ready, busy}, request : boolean`
|                      `init(state) := ready`
|                      `next(state) := if state = ready & request = TRUE`
|                      `then busy else {ready, busy}`
| type systems         `4 : Int`
|                      `[1,2,4] : List Int`
|                      `(+) 4 : Int → Int`
|                      `(+) : Num a ⇒ a → a → a`
| formal verification* Fóthi, Horváth et al.
|                      B method, Hoare-logic, Coq
| 
| -------------------------
| 
| *give examples
| 
| Remark: we use `:` as the type-of predicate and `∷` as the list constructor
| 
| 
| Type systems
| ============
| 
| Problem:
| 
|     +─────────────────────────+
|     |all programs             |
|     |        +─────────────+  |
|     |        |well-typed  ?|  |
|     |        |programs   ? |  |
|     |     +──+──────────+  |  |
|     |     |  |XXXXXXXXXX|  |  |
|     |     |  |XXXXXXXXXX|  |  |
|     |     |  ───────────+──+  |
|     |     |good programs|     |
|     |     +─────────────+     |
|     +─────────────────────────+
| 
| Solution: more expressive and fine-grained type systems
| 
| 
| Examples of Haskell type system limits
| ======================================
| 
| [`Data.Word`](http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-Word.html)
| 
| [`HaskellDB`](http://hackage.haskell.org/packages/archive/haskelldb/2.1.1/doc/html/Database-HaskellDB-BoundedList.html#t:N255)
| 
| [Square matrices](http://www.eecs.usma.edu/webs/people/okasaki/icfp99.ps)
| 
| More: types of fixed-length lists, sorted lists, balanced trees, numbers that are between 13 and 45 etc.
| 
| Fixing Haskell 98: [MultiParamTypeClasses](http://hackage.haskell.org/trac/haskell-prime/wiki/MultiParamTypeClasses), [GADTs](http://hackage.haskell.org/trac/haskell-prime/wiki/GADTs), [FunctionalDependencies](http://hackage.haskell.org/trac/haskell-prime/wiki/FunctionalDependencies), [RankNTypes](http://hackage.haskell.org/trac/haskell-prime/wiki/RankNTypes), [KindAnnotations](http://hackage.haskell.org/trac/haskell-prime/wiki/KindAnnotations) etc.
| 
| 
| What is Agda?
| =============
| 
| Agda is a programming language with a type system so expressive that makes it a formal verification tool.
| 
-->


Benefits of completing this tutorial
==========

After completing this tutorial, you will be able to:

-   Use Agda directly (you have to put more effort in learning Agda for this)

    -   develop formal systems, use Agda in research
    -   write high-assurance code  
        Note that the current compiler is not industrial-strength, libraries are missing,  
        solutions for individual problems are not worked out.

-   Learn similar languages easier

    -   most Haskell type system extensions are just special cases
        -   Haskell is a practical general-purpose programming language also used in industry.

    -   languages with similar goals: Coq, Idris, Epigram
        -   write formal proofs in Coq which is more mainstream

-   Use the ideas presented here

    -   have a better programming style / understanding in other languages
    -   steal the ideas

-   Learn related theoretical concepts easier (which will be more familiar for you)

    -   type theory
        -   dependent types

    -   constructive mathematics
    -   semantics of programming languages
        -   λ-calculus
