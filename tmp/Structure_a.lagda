% Structure of Set Elements
% Péter Diviánszky
% 2011. 07. 30.

\begin{code}
module Structure_a where
\end{code}


Open Expressions
================

An expression is *open* if it contains one or more free variables.

Open expressions:

    n
    suc n
    suc (suc n)
    n ≤ suc m
    A ⊎ Bool

Closed expressions:

    zero
    suc zero ≤ suc zero


Partial Information
===================

Open expressions contain partial information:

-   `suc n` -- a natural number which is at least 1; its predessor is `n`
-   `suc (suc n)` -- a natural number which is at least 2; `n` is the number minus 2.
-   `n ≤ suc m`  -- `n` is strictly less than `m`.
-   `A ⊎ Bool`  -- `A` is a set (no other information).

The information can propagate in several direction:

-   `z≤n i : a ≤ b`  --  `a` is `zero` and `i` equals to `b` (info from `z≤n`).
-   `e : suc a ≤ suc b`  -- `e` is `s≤s x` for some `x` (info from the type).
-   `z≤n i : a ≤ suc zero`  --  `a` is `zero` and `i` is `suc zero`.
-   `s≤s e : a ≤ zero`  --  Impossible case; we can derive a contradiction from this.

A big part of these information are deduced and propagated by Agda.

------------------

We can help Agda if it cannot deduce or propagate these kind of information; see later.


Exercises
=========


Practical Aspects
=================

The structure of set elements matters.

-   It is easy to proof that `n ≤′ n`; it is not-so-easy to proof that `n ≤ n`.

`≤′-step e : n ≤′ m`
`s≤s e : n ≤ m`

_ : ℕ → ℕ → Set  where
  z≤n : (n : ℕ)           → zero  ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n






