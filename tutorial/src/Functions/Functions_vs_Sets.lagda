% Functions vs. Sets

\begin{code}
module Functions.Functions_vs_Sets where

open import Sets.Enumerated using (Bool; true; false)
\end{code}

Now, that we have seen sets and functions, it may make sense to compare them
and discuss the observed differences.

Negation as a relation
============================

Recall how the logical negation can be represented as a relation between
values of the `Bool` and `Bool` sets:

\begin{code}
data Not : Bool → Bool → Set where
  n₁ : Not true false
  n₂ : Not false true
\end{code}

Note that this will create four new sets of which two are non-empty.

`Not a b` is non-empty iff `b` is the negated value of `a`.


Negation as a function
============================

Now consider the representation of the negation as a function:

\begin{code}
not : Bool → Bool
not true  = false
not false = true
\end{code}


Relations vs. functions
=====================

Benefits of using relations:

-   Less restrictions:

    -   not all the cases should be covered (partial specification)
    -   redundancy is allowed
    -   general recursion is allowed
    -   inconsistency is allowed (that is, an empty relation)

-   Shorter definitions (the difference increases with complexity)

Benefits of using functions:

-   More and better guarantees:

    -   *coverage check* ensures that all cases are covered
    -   *reachability check* excludes redundant cases
    -   *termination check* ensures termination for recursion
    -   inconsistency is excluded *by construction*

-   Functions have computational content:

    -   code generation is possible
    -   shorter proofs (see later)

-   Ease of use, cf. `not (not a)` and `Not a b ∧ Not b c`


Specification vs. implementation
=====================

- Relations are useful for describing the problem/question (that is, a
  *specification*).

- Functions are useful for describing the solution/answer (that is, an
  *implementation*).

Remarks:

- Implementations are connected to specifications by the type system (see later).

- Functions are also used in specifications due to their ease of use and because
  they can conveniently represent negation and universal quantification.

    - Just like in mathematics where definitions may rely on previously known
      theorems.

Functions with a Boolean value (predicates)
===========================================

An `A → B → C` function corresponds to the specification `A → B → C → Set`
according the previous remarks.  That is, `_≤?_ : ℕ → ℕ → Bool` would
correspond to `ℕ → ℕ → Bool → Set`, but actually it is easier to define
Boolean-valued functions, so we have `_≤_ : ℕ → ℕ → Set` as specification.
