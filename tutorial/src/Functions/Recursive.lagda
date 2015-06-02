% Recursive Functions

\begin{code}
module Functions.Recursive where
\end{code}

Import list
===========

\begin{code}
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; zero)
\end{code}

Functions can be recursive as well, which is essential for working on sets that
were defined recursively.  In this case, a common approach is to define an
alternative for each of the constructors and when the constructor is recursive
then the function itself shall also be probably recursive.

`_+_`: Addition
===============

Consider the previous definition of the `ℕ` type, where we had the following
constructors with the following types:

`zero : ℕ`  
`suc  : ℕ → ℕ`

Note that this was done along the lines of the mathematical definition of the
Peano arithmetic.  Consider also the definion of how to calculate the sum of
two natural numbers with this representation:

$\begin{array}{rcl}0 + n & = & n \\ (1 + m) + n & = & 1 + (m + n) \end{array}$

Now consider the same definition in Agda:

\begin{code}
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

infixl 6 _+_
\end{code}

Exercises
---------

Define the following functions:

~~~~{.agda}
pred  : ℕ → ℕ      -- predecessor (pred 0 = 0)

infixl 6 _∸_
_∸_   : ℕ → ℕ → ℕ  -- subtraction (0 ∸ n = n)

infixl 7 _*_
_*_   : ℕ → ℕ → ℕ  -- multiplication

infixl 6 _⊔_
_⊔_   : ℕ → ℕ → ℕ  -- maximum

infixl 7 _⊓_
_⊓_   : ℕ → ℕ → ℕ  -- minimum

⌊_/2⌋ : ℕ → ℕ      -- half (⌊ 1 /2⌋ = 0)

odd   : ℕ → Bool   -- is odd

even  : ℕ → Bool   -- is even
~~~~

<!--
\begin{code}
pred  : ℕ → ℕ      -- predecessor (pred 0 = 0)
pred zero    = zero --
pred (suc n) = n --
\end{code}
-->

<!--
\begin{code}
infixl 6 _∸_
_∸_   : ℕ → ℕ → ℕ  -- subtraction (0 ∸ n = n)
zero  ∸ _     = zero --
suc n ∸ zero  = suc n --
suc n ∸ suc m = n ∸ m --
\end{code}
-->

<!--
\begin{code}
infixl 7 _*_
_*_   : ℕ → ℕ → ℕ  -- multiplication
zero  * _ = zero --
suc n * b = b + n * b --
\end{code}
-->

<!--
\begin{code}
infixl 6 _⊔_
_⊔_   : ℕ → ℕ → ℕ  -- maximum
zero  ⊔ b     = b --
a     ⊔ zero  = a --
suc a ⊔ suc b = suc (a ⊔ b) --
\end{code}
-->

<!--
\begin{code}
infixl 7 _⊓_
_⊓_   : ℕ → ℕ → ℕ  -- minimum
zero  ⊓ _     = zero --
_     ⊓ zero  = zero --
suc a ⊓ suc b = suc (a ⊓ b) --
\end{code}
-->

<!--
\begin{code}
⌊_/2⌋ : ℕ → ℕ      -- half (⌊ 1 /2⌋ = 0)
⌊ zero /2⌋        = zero --
⌊ suc zero /2⌋    = zero --
⌊ suc (suc n) /2⌋ = suc ⌊ n /2⌋ --
\end{code}
-->

<!--
\begin{code}
-- odd zero          = false --
-- odd (suc zero)    = true --
-- odd (suc (suc n)) = odd n --
\end{code}
-->

<!--
\begin{code}
-- even zero          = true --
-- even (suc zero)    = false --
-- even (suc (suc n)) = even n --
\end{code}
-->

Mutual definitions
==================

It is possible to define functions mutually, like we did for sets.  As an
example, consider the mutual definition of the `even` and `odd` functions:

~~~~{.agda}
odd : ℕ → Bool

even : ℕ → Bool
even zero    = true
even (suc n) = odd n

odd zero    = false
odd (suc n) = even n
~~~~

Exercises
---------

Define the following functions mutually:

\begin{code}
_≡?_  : ℕ → ℕ → Bool  -- is equal
_≤?_  : ℕ → ℕ → Bool  -- is less than or equal
\end{code}

<!--
\begin{code}
zero  ≡? zero  = true --
zero  ≡? suc _ = false --
suc _ ≡? zero  = false --
suc n ≡? suc m = n ≡? m --
\end{code}
-->
<!--
\begin{code}
zero  ≤? _     = true --
suc _ ≤? zero  = false --
suc n ≤? suc m = n ≤? m --
\end{code}
-->

Binary representation of `ℕ`
============================

Import the binary representation of natural numbers:

\begin{code}
open import Sets.Recursive using (ℕ⁺; one; double; double+1; ℕ₂; zero; id)
\end{code}

Exercise
--------

Define a conversion function of the following type:

\begin{code}
from : ℕ₂ → ℕ  -- hint: use _*_
\end{code}

<!--
\begin{code}
from zero              = zero --
from (id one)          = suc zero --
from (id (double n))   = suc (suc zero) * from (id n) --
from (id (double+1 n)) = suc (suc (suc zero) * from (id n)) --
\end{code}
-->

Note that the `from` function shall define a reverse function of the following
isomorphism between `ℕ` and `ℕ₂` (later we will prove that `from` is an
isomorphism):

**ℕ**                   **ℕ₂**
----------------------- --------------------------
`zero`                  `zero`
`suc zero`              `id one`
`suc (suc zero)`        `id (double one)`
`suc (suc (suc zero))`  `id (double+1 one)`
...                     ...

Later we will see how to define the same conversion in the other direction.

Exercises
---------

Define `ℤ` and some operations on it (such as `_+_`, `_-_`, `_*_`).

Binary trees
=========

\begin{code}
data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree
\end{code}

Exercise
--------

Define (recursive) mirroring of binary trees, that is a function with the
following type:

`mirror : BinTree → BinTree`
