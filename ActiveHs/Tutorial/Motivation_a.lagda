% Motivation
% Ambrus Kaposi, Péter Diviánszky
% 2012. 02. 13., 2013. 01.

\begin{code}
module Motivation_a where
\end{code}


About the tutorial
==================

Goals

- show what is Agda good for
- teach Agda syntax and semantics
- teach Agda programming skills

Features

- slides: 1/3 examples, 1/3 explanation, 1/3 exercises
- only (part of) secondary school mathematics is required

----------------

Pressing key 'a' on the pages switch between slide and normal mode.  
Navigation is possible with left and right arrows.  
In slide mode the remarks are not visible!

The developers are Péter Diviánszky and Ambrus Kaposi. Any comment is very much appreciated, please send them to Péter (divipp at gmail).

[*More about the tutorial*](About_a.xml)


What is Agda good for?
=====================

**To utilize the capacity of computers in a reliable way.**

Target:  

programming and mathematics;  
formal definitions, theorems, proofs and algorithms


Benefits of programming in Agda
===============================

-   **eliminating errors**
    -   no runtime errors  
        Inevitable errors like I/O errors are handled, others are excluded by design.
    -   no non-productive infinite loops
-   **machine checked documentation**  
    Any functional properties can be formalized and proved; proof checking is automatic.  
    -   distinction between finite and infinite data like lists vs. streams
    -   invariant properties of data like sorted list, balanced tree can be maintained
    -   function properties like commutativity, associativity can be maintained
-   **exact interfaces**  
    Formal specification can be given with the help of exact mathematical concepts like 
    groups, rings, lattices, categories, ...
-   **safe optimization**
    -   runtime checks like array index bounds checks are eliminated
    -   defensive coding (generous on input, strict on output) is unnecessary -- no overhead of it
    -   safe optimization on special input like associative input function of a higher order function
-   **high level programming**
    -   programming with types as data (generic programming, universes)  
        Type may depend on runtime value and still checked in compile time.
    -   reflection
    -   Previously unseen range of embedded domain specific languages
        can be defined with arbitrary precision.



Benefits of creating formal systems in Agda
==============================

Definitions

-   classical, constructive and modal logical connectives are definable

Theorems

-   one can quantify over elements, properties,
    properties of properties etc.  
    (Agda has the strength of an infinite-order logic)

Proofs

-   Automatic simplification of expressions gives the
    automatic part of proofs.  
    In this way algorithms can be used during proofs.
-   automatic proof checking

Additional features

-   inferred terms, implicit arguments
-   holes, interactive development
-   unicode characters, misfix operators




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


Benefits of completing the tutorial
==========

-   use Agda directly (you have to put more effort in learning Agda for this)
    -   develop formal systems, use Agda during research
    -   write high-assurance code  
        Note that the current compiler is not industrial-strength, libraries are missing,  
        solutions for individual problems are not worked out.
-   learn similar languages easier
    -   most Haskell type system extensions are just special cases
        -   Haskell is practical general-purpose programming language also used in industry.
    -   languages with similar goals: Coq, Idris, Epigram
        -   write formal proofs in Coq which is more mainstream
-   use the ideas presented here
    -   have a better programming style / understanding in other languages
    -   steel the ideas
-   learn theory easier (will be more familiar for you)
    -   type theory
        -   dependent types
    -   constructive mathematics
    -   semantics of programming languages
        -   λ-calculus






