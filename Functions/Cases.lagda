% Functions Defined by Cases
% Péter Diviánszky
% 2011. 05. 03.

\begin{code}
module Functions.Cases where
\end{code}


The `Bool` set
==============

Remember the definition of `Bool`:

\begin{code}
data Bool : Set where
  true  : Bool
  false : Bool
\end{code}


Boolean NOT as a relation
============================

Definition of NOT as a relation:

\begin{code}
data Not : Bool → Bool → Set where
  n₁ : Not true false
  n₂ : Not false true
\end{code}

This creates four new sets from which two are non-empty.

`Not a b` is non-empty iff `b` is the negated value of `a`.

**********

`not` is a function that has `Bool` as domain and `Bool` as range.
We can pattern match on the elements that appear in set `Bool` namely `true` and `false` to define how the function works.



Boolean NOT as a function
============================

Definition of NOT as a function:

\begin{code}
not : Bool → Bool
not true  = false
not false = true
\end{code}

This adds elements to `Bool` like

`not true : Bool`  
`not (not (not false)) : Bool`  

but these are not new elements (they are not in *canonical form*).

`not a` is the negated value of `a`.

The definition has a *computational content*, i.e. how to compute
the negated value.


Relations vs. functions
=====================

Relation advantages:

-   Less restrictions
    -   not all cases should be covered (partial specification)
    -   redundancy is allowed
    -   general recursion is allowed
    -   inconsistency is allowed (resulting in an empty relation)
-   Shorter and easier to compose than corresponding functions  
    (the difference increases with complexity)

Function advantages:

-   More guarantees
    -   coverage check ensures that all cases are covered 
    -   reachability check excludes multiple cases  
    -   termination check ensures terminating recursion
    -   inconsistency is excluded by construction
-   Computational content (reduction to normal form)
    -   code generation
    -   simplified equality proofs (at compile time; see later)
-   Easier to use  
    `not (not a)` instead of `Not a b ∧ Not b c`

Specification vs. implementation
=====================

Relations are good for describing the problem/question (**specification**).

Functions are good for describing the solution/answer (**implementation**).

*Notes*

-   Implementations are connected to specifications by the type system (see later).  
    "Programming without types is like giving the answer without knowing the question."
-   Functions are used in specifications too because of advantages
    "easier to use" and "simplified equality proofs".
    -   like in mathematics where definitions
        may need theorems in advance



Logical AND
===============================

Definition:
 
\begin{code}
_∧_   : Bool → Bool → Bool
true  ∧ x = x
false ∧ _ = false

infixr 6 _∧_
\end{code}

*********

-   We can use variables as patterns.
-   We can use wildcard (an underscore) as pattern.
-   Logical AND could be defined with four alternatives.
-   Similar to data sets
    -   Underscores in names like `_∧_` denote the space for the operands.
    -   `infixr` gives the fixity


Exercise: `_∨_`
=========


A) Define logical OR:

\begin{code}
infixr 5 _∨_
 
_∨_   : Bool → Bool → Bool
\end{code}

<!--
\begin{code}
true  ∨ _ = true --
false ∨ x = x --
\end{code}
-->
 
B) Define logical OR with one alternative, with the help of `not` and `_∧_`!

<!--
\begin{code}
infixr 5 _∨₁_ --

_∨₁_   : Bool → Bool → Bool --
x ∨₁ y = not (not x ∧ not y) --
\end{code}
-->
 
Exercises
=========

A)  Define a set named `Answer` with three elements, `yes`, `no` and `maybe`.

    Define logical operations on `Answer`!
 
B)  Define a set named `Quarter` with four elements, `east`, `west`, `north` and `south`.

    Define a function `turnLeft : Quarter → Quarter`.
 
    Define the functions `turnBack` and `turnRight` with the help of `turnLeft`! (By either pattern matching  or defining specific function composition function.)




