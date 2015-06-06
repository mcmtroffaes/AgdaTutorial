% Decimal Notation for Natural Numbers


\begin{code}
module Syntax.Decimal_Naturals where
\end{code}


Constants in Peano Representation
================================

Peano representation of natural number constants
which are greater than three are hard to read:

    suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))

On the other hand, decimal representation which we are used to is
easy to read:

    12


Decimal notation for Peano representation
=========================================

Agda's solution is to *keep* the Peano representation while
giving a decimal notation for constants in Peano representation.

For example,

    3

will be a shorthand for

    suc (suc (suc zero))


Technical details
===========

Agda needs special directives to allow decimal
notations of constants in Peano representation:

    data ℕ : Set where
      zero :     ℕ
      suc  : ℕ → ℕ

    {-# BUILTIN NATURAL ℕ #-}


Unfortunately, this `BUILTIN` machinery is not designed to accommodate multiple
definitions of a given `BUILTIN`.
If we wish to use definitions from the Standard Libraries later (and we wish),
we cannot make another Peano representation of naturals *with* decimal notation.

The solution is to reuse the existing the `ℕ`, `zero`, and `suc` definitions
with decimal notation from the Standard Libraries:

\begin{code}
open import Data.Nat public using (ℕ; zero; suc)
\end{code}

(Import declarations will be discussed later.)
