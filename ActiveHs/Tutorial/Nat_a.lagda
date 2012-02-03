% Natural Numbers
% Péter Diviánszky
% 2011. 05. 03.

\begin{code}
module Nat_a where
\end{code}


Definition of `ℕ`
==============

Definition of `ℕ`:

\begin{code}
data ℕ : Set where
  zero :     ℕ
  suc  : ℕ → ℕ
\end{code}

*Interpretation:* `ℕ` ∈ `Set`, `ℕ` = { `zero`, `suc zero`, `suc (suc zero)`, ... }

We may use `0`, `1`, `2`, ... instead of `zero`, `suc zero`, ...*

************************

*\ Decimal natural number literals can be used if we bind our `ℕ` set to the Agda internals with the following three declarations:

\begin{code}
{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}
\end{code}


`_+_`: Addition
==================

Definition of addition:

\begin{code}
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

infixl 6 _+_
\end{code}



Exercises: `pred`, `_*_`, `_⊔_`, `_⊓_` and `⌊_/2⌋`
=========

Define the following functions:

~~~~~~~ {.haskell}
pred  : ℕ → ℕ      -- predessor (pred 0 = 0)
_∸_   : ℕ → ℕ → ℕ  -- subtraction
_*_   : ℕ → ℕ → ℕ  -- multiplication
_⊔_   : ℕ → ℕ → ℕ  -- maximum
_⊓_   : ℕ → ℕ → ℕ  -- minimum
⌊_/2⌋ : ℕ → ℕ      -- half (⌊ 1 /2⌋ = 0)
odd   : ℕ → Bool   -- is odd
even  : ℕ → Bool   -- is even
_≡?_  : ℕ → ℕ → Bool  -- is equal
_≤?_  : ℕ → ℕ → Bool  -- is less than or equal
~~~~~~~


Alternative Definition of `ℕ`
==============

\begin{code}
data ℕ⁺ : Set where
  one      :      ℕ⁺
  double   : ℕ⁺ → ℕ⁺
  double+1 : ℕ⁺ → ℕ⁺

data ℕ₂ : Set where
  zero :      ℕ₂
  id   : ℕ⁺ → ℕ₂
\end{code}

*Interpretation:*

 - `ℕ⁺` ∈ `Set`, `ℕ⁺` = { `one`, `double one`, `double+1 one`, `double (double one)`, `double (double+1 one)`, ...}
 - `ℕ₂` ∈ `Set`, `ℕ₂` = { `zero`, `suc one`, `suc (double one)`, ...}


*Exercise:* define the conversion function:

\begin{code}
from : ℕ₂ → ℕ  -- hint: use _*_
\end{code}

We will see how to define the conversion into the other direction later.

| Now all other operations on ℕ₂ can be defined via conversion to
| ℕ, but try to give faster definitions!

*Question*: why didn't we use one `data` definition with 4 constructors `zero`, `one`, `double`, `double+1`?

Exercise
========

Define `ℤ` and some operations on it (at least `_+_`, `_-_`, `_*_`)!
