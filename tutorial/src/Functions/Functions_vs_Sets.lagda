% Functions vs. Sets

\begin{code}
module Functions.Functions_vs_Sets where

open import Sets.Enumerated using (Bool; true; false)
\end{code}


Negation as a relation
============================

Representation of negation as a relation between `Bool` and `Bool`:

\begin{code}
data Not : Bool → Bool → Set where
  n₁ : Not true false
  n₂ : Not false true
\end{code}

This creates four new sets of which two are non-empty.

`Not a b` is non-empty iff `b` is the negated value of `a`.


Negation as a function
============================

Recall the representation of negation as a function:

\begin{code}
not : Bool → Bool
not true  = false
not false = true
\end{code}


Relations vs. functions
=====================

Relation's advantages:

-   Less restrictions
    -   not all cases should be covered (partial specification)
    -   redundancy is allowed
    -   general recursion is allowed
    -   inconsistency is allowed (resulting in an empty relation)
-   Shorter definitions
    (the difference increases with complexity)

Function's advantages:

-   More guarantees
    -   coverage check ensures that all cases are covered 
    -   reachability check excludes multiple cases  
    -   termination check ensures terminating recursion
    -   inconsistency is excluded by construction
-   Functions have computational content
    -   code generation possibility
    -   shorter proofs (see later)
-   Easier to use  
    `not (not a)` instead of `Not a b ∧ Not b c`


Specification vs. implementation
=====================

Relations are good for describing the problem/question (**specification**).

Functions are good for describing the solution/answer (**implementation**).

*Notes*

-   Implementations are connected to specifications by the type system (see later).  
-   Functions are used in specifications too because of the advantage
    "easier to use" and they can represent negation and universal quantification.
    -   like in mathematics where definitions
        may need theorems in advance


Functions with Boolean value
============================

*Remark*

An `A → B → C` function
corresponds to specification
`A → B → C → Set` according our previous remark.
So `_≤?_ : ℕ → ℕ → Bool` would correspond to `ℕ → ℕ → Bool → Set`,
but Boolean valued functions can be specified easier
so we have `_≤_ : ℕ → ℕ → Set` as specification.




