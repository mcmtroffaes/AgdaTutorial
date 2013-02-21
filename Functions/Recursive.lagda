% Recursive Functions

\begin{code}
module Functions.Recursive where
\end{code}

Import List
===========

\begin{code}
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; zero)
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
\end{code}

<!--
\begin{code}
pred zero    = zero --
pred (suc n) = n --
\end{code}
-->

\begin{code}
infixl 6 _∸_
_∸_   : ℕ → ℕ → ℕ  -- subtraction (0 ∸ n = n)
\end{code}

<!--
\begin{code}
zero  ∸ _     = zero --
suc n ∸ zero  = suc n --
suc n ∸ suc m = n ∸ m --
\end{code}
-->

\begin{code}
infixl 7 _*_
_*_   : ℕ → ℕ → ℕ  -- multiplication
\end{code}

<!--
\begin{code}
zero  * _ = zero --
suc n * b = b + n * b --
\end{code}
-->

\begin{code}
infixl 6 _⊔_
_⊔_   : ℕ → ℕ → ℕ  -- maximum
\end{code}

<!--
\begin{code}
zero  ⊔ b     = b --
a     ⊔ zero  = a --
suc a ⊔ suc b = suc (a ⊔ b) --
\end{code}
-->

\begin{code}
infixl 7 _⊓_
_⊓_   : ℕ → ℕ → ℕ  -- minimum
\end{code}

<!--
\begin{code}
zero  ⊓ _     = zero --
_     ⊓ zero  = zero --
suc a ⊓ suc b = suc (a ⊓ b) --
\end{code}
-->

\begin{code}
⌊_/2⌋ : ℕ → ℕ      -- half (⌊ 1 /2⌋ = 0)
\end{code}

<!--
\begin{code}
⌊ zero /2⌋        = zero --
⌊ suc zero /2⌋    = zero --
⌊ suc (suc n) /2⌋ = suc ⌊ n /2⌋ --
\end{code}
-->

Exercises: `even`, `odd`
=========

\begin{code}
odd   : ℕ → Bool   -- is odd
\end{code}

<!--
\begin{code}
odd zero          = false --
odd (suc zero)    = true --
odd (suc (suc n)) = odd n --
\end{code}
-->

\begin{code}
even  : ℕ → Bool   -- is even
\end{code}

<!--
\begin{code}
even zero          = true --
even (suc zero)    = false --
even (suc (suc n)) = even n --
\end{code}
-->

Mutual definitions
=========

Define `even` and `odd` mutually with the `mutual` keyword!


Exercises: `_≡?_`, `_≤?_`
=========


\begin{code}
_≡?_  : ℕ → ℕ → Bool  -- is equal
\end{code}

<!--
\begin{code}
zero  ≡? zero  = true --
zero  ≡? suc _ = false --
suc _ ≡? zero  = false --
suc n ≡? suc m = n ≡? m --
\end{code}
-->

\begin{code}
_≤?_  : ℕ → ℕ → Bool  -- is less than or equal
\end{code}

<!--
\begin{code}
zero  ≤? _     = true --
suc _ ≤? zero  = false --
suc n ≤? suc m = n ≤? m --
\end{code}
-->

Functions with Boolean value
============================

*Remark*

An `A → B → C` function
corresponds to specification
`A → B → C → Set` according our previous remark.
So `_≤?_ : ℕ → ℕ → Bool` would correspond to `ℕ → ℕ → Bool → Set`,
but Boolean valued functions can be specified easier
so we have `_≤_ : ℕ → ℕ → Set` as specification.

We give the theory behind this later.



Binary representation of `ℕ`
==============

Import the binary representation of natural numbers:

\begin{code}
open import Sets.Recursive using (ℕ⁺; one; double; double+1; ℕ₂; zero; id)
\end{code}

*Exercise:* define the conversion function:

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

`from` should define the backward function of the following isomorphism between `ℕ` and `ℕ₂`
(we prove that `from` is an isomorphism later):

**ℕ**                   **ℕ₂**
----------------------- --------------------------
`zero`                  `zero`
`suc zero`              `id one`
`suc (suc zero)`        `id (double one)`
`suc (suc (suc zero))`  `id (double+1 one)`
...                     ...


We will see how to define the conversion to the other direction later.



Exercises
=========

Define `ℤ` and some operations on it (`_+_`, `_-_`, `_*_`)!


Binary trees
=========

\begin{code}
data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree
\end{code}

*Exercise:* define (recursive) mirroring of binary trees!





