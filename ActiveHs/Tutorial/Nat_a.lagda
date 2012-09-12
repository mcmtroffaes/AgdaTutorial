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

*Interpretation:* `ℕ` ∈ `Set`, `ℕ` = { `zero` ~ 0, `suc zero` ~ 1, `suc (suc zero)` ~ 2, ... }

We may use `0`, `1`, `2`, ... instead of `zero`, `suc zero`, ...*

************************

*\ Decimal natural number literals can be used if we bind our `ℕ` set to the Agda internals with the following three declarations:

\begin{code}
{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}
\end{code}


Set element definitions
=======================

\begin{code}
nine : ℕ
nine = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

ten : ℕ
ten = suc nine
\end{code}

The type signature is optional.



| `_+_`: Addition
| ==================
| 
| Definition of addition:
| 
| \begin{code}
| _+_ : ℕ → ℕ → ℕ
| zero  + n = n
| suc m + n = suc (m + n)
| 
| infixl 6 _+_
| \end{code}
| 
| 
| Exercises: `pred`, `_*_`, `_⊔_`, `_⊓_` and `⌊_/2⌋`
| =========
| 
| Define the following functions:
| 
| \begin{code}
| pred  : ℕ → ℕ      -- predecessor (pred 0 = 0)
| pred zero    = zero --
| pred (suc n) = n --
| \end{code}
| 
| \begin{code}
| infixl 6 _∸_
| _∸_   : ℕ → ℕ → ℕ  -- subtraction
| zero  ∸ _     = zero --
| suc n ∸ zero  = suc n --
| suc n ∸ suc m = n ∸ m --
| \end{code}
| 
| \begin{code}
| infixl 7 _*_
| _*_   : ℕ → ℕ → ℕ  -- multiplication
| zero  * _ = zero --
| suc n * b = b + n * b --
| \end{code}
| 
| \begin{code}
| infixl 6 _⊔_
| _⊔_   : ℕ → ℕ → ℕ  -- maximum
| zero  ⊔ b     = b --
| a     ⊔ zero  = a --
| suc a ⊔ suc b = suc (a ⊔ b) --
| \end{code}
| 
| \begin{code}
| infixl 7 _⊓_
| _⊓_   : ℕ → ℕ → ℕ  -- minimum
| zero  ⊓ _     = zero --
| _     ⊓ zero  = zero --
| suc a ⊓ suc b = suc (a ⊓ b) --
| \end{code}
| 
| \begin{code}
| ⌊_/2⌋ : ℕ → ℕ      -- half (⌊ 1 /2⌋ = 0)
| ⌊ zero /2⌋        = zero --
| ⌊ suc zero /2⌋    = zero --
| ⌊ suc (suc n) /2⌋ = suc ⌊ n /2⌋ --
| \end{code}
| 
| \begin{code}
| odd   : ℕ → Bool   -- is odd
| odd zero          = false --
| odd (suc zero)    = true --
| odd (suc (suc n)) = odd n --
| \end{code}
| 
| \begin{code}
| even  : ℕ → Bool   -- is even
| even zero          = true --
| even (suc zero)    = false --
| even (suc (suc n)) = even n --
| \end{code}
| 
| \begin{code}
| _≡?_  : ℕ → ℕ → Bool  -- is equal
| zero  ≡? zero  = true --
| zero  ≡? suc _ = false --
| suc _ ≡? zero  = false --
| suc n ≡? suc m = n ≡? m --
| \end{code}
| 
| \begin{code}
| _≤?_  : ℕ → ℕ → Bool  -- is less than or equal
| zero  ≤? _     = true --
| suc _ ≤? zero  = false --
| suc n ≤? suc m = n ≤? m --
| \end{code}

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

 - `ℕ⁺` ∈ `Set`, `ℕ⁺` = { `one` ~ 1, `double one` ~ 2, `double+1 one` ~ 3, `double (double one)` ~ 4, `double (double+1 one)` ~ 5, ...}
 - `ℕ₂` ∈ `Set`, `ℕ₂` = { `zero` ~ 0, `id one` ~ 1, `id (double one)` ~ 2, ...}

*Exercise:* define `nine : ℕ₂`!


| *Exercise:* define the conversion function:
| 
| \begin{code}
| from : ℕ₂ → ℕ  -- hint: use _*_
| from zero              = zero --
| from (id one)          = suc zero --
| from (id (double n))   = 2 * from (id n) --
| from (id (double+1 n)) = suc (2 * from (id n)) --
| \end{code}
| 
| We will see how to define the conversion to the other direction later.

*Question*: why didn't we use one `data` definition with 4 constructors `zero`, `one`, `double`, `double+1`?


Soon we will prove in Agda that `ℕ` and `ℕ₂` are isomorphic with the following relation:

**ℕ**                   **ℕ₂**
----------------------- --------------------------
`zero`                  `zero`
`suc zero`              `id one`
`suc (suc zero)`        `id (double one)`
`suc (suc (suc zero)`   `id (double+1 one)`




Exercises
=========

A) Define `ℤ`!
|  and some operations on it (at least `_+_`, `_-_`, `_*_`)!

B) Define `ℚ`!

(Several solutions are possible.)


Binary trees
=========

The set of binary trees (just the shapes without data):

\begin{code}
data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree
\end{code}

*Exercise:* define binary trees according to the following shapes!

~~~~~~~~ {.dot}
Node [shape = point]
Edge [dir = none]
z
o -> z1
o -> z2
x -> a
x -> b
a -> a1
a -> a2
b -> b1
b -> b2
x1 -> x2 -> x3 -> x4
x1 -> x1v
x2 -> x2v
x3 -> x3v
~~~~~~~~


Infix notation
==============



\begin{code}
data BinTree' : Set where
  x : BinTree'
  _+_ : BinTree' → BinTree' → BinTree'

t : BinTree'
t = (x + x) + (x + x)
\end{code}

Underscores in names like `_+_` denote the space for the operands.  

One can give the precedence with `infix`, `infixl` or `infixr`:

\begin{code}
infixr 3 _+_

t' : BinTree'
t' = (x + x) + x + x
\end{code}




Exercises
=========

A) Define binary trees

-   with natural number data attached to the leafs
-   with natural number data attached to the nodes
-   with Booleans in the nodes and natural numbers in the leafs

B) Define the lists of natural numbers! Use `_∷_` as list consructor with right precedence!

C) Define the non-empty lists of natural numbers!

D) Define trees with nodes with finite children (0, 1, 2, ...)!


Mutual definitions
=========


\begin{code}
mutual
  data L : Set where
    nil : L
    _∷_ : ℕ → M → L

  data M : Set where
    _∷_ : Bool → L → M
\end{code}

*Exercise*: What are the elements of `L` and `M`?


Exercise
=========

Define a small grammar!*

-------

*highly underspecified exercise


