% Natural Numbers
% Péter Diviánszky
% 2011. 05. 03.

\begin{code}
module Nat_a where
\end{code}

Import List
===========

\begin{code}
open import Data.Bool using (Bool; true; false)
\end{code}

This opens and imports `Data.Bool` from the standard library. Without `open` we could only refer to the functions imported with qualified name such as `Data.Bool.bool`.

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

\begin{code}
pred  : ℕ → ℕ      -- predecessor (pred 0 = 0)
pred zero    = zero --
pred (suc n) = n --
\end{code}

\begin{code}
infixl 6 _∸_
_∸_   : ℕ → ℕ → ℕ  -- subtraction
zero  ∸ _     = zero --
suc n ∸ zero  = suc n --
suc n ∸ suc m = n ∸ m --
\end{code}

\begin{code}
infixl 7 _*_
_*_   : ℕ → ℕ → ℕ  -- multiplication
zero  * _ = zero --
suc n * b = b + n * b --
\end{code}

\begin{code}
infixl 6 _⊔_
_⊔_   : ℕ → ℕ → ℕ  -- maximum
zero  ⊔ b     = b --
a     ⊔ zero  = a --
suc a ⊔ suc b = suc (a ⊔ b) --
\end{code}

\begin{code}
infixl 7 _⊓_
_⊓_   : ℕ → ℕ → ℕ  -- minimum
zero  ⊓ _     = zero --
_     ⊓ zero  = zero --
suc a ⊓ suc b = suc (a ⊓ b) --
\end{code}

\begin{code}
⌊_/2⌋ : ℕ → ℕ      -- half (⌊ 1 /2⌋ = 0)
⌊ zero /2⌋        = zero --
⌊ suc zero /2⌋    = zero --
⌊ suc (suc n) /2⌋ = suc ⌊ n /2⌋ --
\end{code}

\begin{code}
odd   : ℕ → Bool   -- is odd
odd zero          = false --
odd (suc zero)    = true --
odd (suc (suc n)) = odd n --
\end{code}

\begin{code}
even  : ℕ → Bool   -- is even
even zero          = true --
even (suc zero)    = false --
even (suc (suc n)) = even n --
\end{code}

\begin{code}
_≡?_  : ℕ → ℕ → Bool  -- is equal
zero  ≡? zero  = true --
zero  ≡? suc _ = false --
suc _ ≡? zero  = false --
suc n ≡? suc m = n ≡? m --
\end{code}

\begin{code}
_≤?_  : ℕ → ℕ → Bool  -- is less than or equal
zero  ≤? _     = true --
suc _ ≤? zero  = false --
suc n ≤? suc m = n ≤? m --
\end{code}

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
 - `ℕ₂` ∈ `Set`, `ℕ₂` = { `zero`, `id one`, `id (double one)`, ...}


*Exercise:* define the conversion function:

\begin{code}
from : ℕ₂ → ℕ  -- hint: use _*_
from zero              = zero --
from (id one)          = suc zero --
from (id (double n))   = 2 * from (id n) --
from (id (double+1 n)) = suc (2 * from (id n)) --
\end{code}

We will see how to define the conversion to the other direction later.

*Question*: why didn't we use one `data` definition with 4 constructors `zero`, `one`, `double`, `double+1`?

Exercise
========

Define `ℤ` and some operations on it (at least `_+_`, `_-_`, `_*_`)!
