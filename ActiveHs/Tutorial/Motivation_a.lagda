% Motivation
% Ambrus Kaposi
% 2012. 02. 13.

\begin{code}
module Motivation_a where
\end{code}



Eliminating errors from programming
===================================

Method               Example
-------------------  ----------------------------------------
run-time monitoring  `Exception in thread "main" java.lang.ArrayIndexOutOfBoundsException`
testing              `quickCheck ((\s → s == s) : List Char → Bool)`
model checking       NuSMV
                     `state : {ready, busy}, request : boolean`
                     `init(state) := ready`
                     `next(state) := if state = ready & request = TRUE`
                     `then busy else {ready, busy}`
type systems         `4 : Int`
                     `[1,2,4] : List Int`
                     `(+) 4 : Int → Int`
                     `(+) : Num a ⇒ a → a → a`
formal verification* Fóthi, Horváth et al.
                     B method, Hoare-logic, Coq

-------------------------

*give examples

Remark: we use `:` as the type-of predicate and `∷` as the list constructor



Type systems
============

Problem:

    +─────────────────────────+
    |all programs             |
    |        +─────────────+  |
    |        |well-typed  ?|  |
    |        |programs   ? |  |
    |     +──+──────────+  |  |
    |     |  |XXXXXXXXXX|  |  |
    |     |  |XXXXXXXXXX|  |  |
    |     |  ───────────+──+  |
    |     |good programs|     |
    |     +─────────────+     |
    +─────────────────────────+

Solution: more expressive and fine-grained type systems




Examples of Haskell type system limits
======================================

[`Data.Word`](http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-Word.html)

[`HaskellDB`](http://hackage.haskell.org/packages/archive/haskelldb/2.1.1/doc/html/Database-HaskellDB-BoundedList.html#t:N255)

[Square matrices](http://www.eecs.usma.edu/webs/people/okasaki/icfp99.ps)

More: types of fixed-length lists, sorted lists, balanced trees, numbers that are between 13 and 45 etc.

Fixing Haskell 98: [MultiParamTypeClasses](http://hackage.haskell.org/trac/haskell-prime/wiki/MultiParamTypeClasses), [GADTs](http://hackage.haskell.org/trac/haskell-prime/wiki/GADTs), [FunctionalDependencies](http://hackage.haskell.org/trac/haskell-prime/wiki/FunctionalDependencies), [RankNTypes](http://hackage.haskell.org/trac/haskell-prime/wiki/RankNTypes), [KindAnnotations](http://hackage.haskell.org/trac/haskell-prime/wiki/KindAnnotations) etc.





What is Agda?
=============

Agda is a programming language with a type system so expressive that makes it a formal verification tool.



Scope of Agda correctness
===================

Good programs

1.  No runtime errors.
    - no type errors
    - no division by zero etc.
    - no pointer errors (null-pointer exception, array index out)
    - empty stack is not popped etc.
2.  The program is productive (reacts to user input / terminates without error).
3.  It gives correct result.
4.  It uses bounded resources (fast enough, predictable memory usage)

Agda guarantees 1-2.*

With Agda one can get as close as necessary to 3.**

There is not much research in 4. with Agda.\***

-------------------

*The program is checked in compile-time once not in run-time many times
so the compiled code can be faster theoretically than in other high-level languages.

**A good programming methodology is needed.

\***Also good for more efficient programs: compile-time garbage-collection etc.



About
=====

Our goal is to give a practical, self contained Agda introduction.

----------------

Pressing key 'a' on the pages switch between slide and normal mode.  
Navigation is possible with left and right arrows.  
In slide mode the remarks are not visible!

The developers are Péter Diviánszky and Ambrus Kaposi. Any comment is very much appreciated, please send them to Péter (divipp at gmail).
