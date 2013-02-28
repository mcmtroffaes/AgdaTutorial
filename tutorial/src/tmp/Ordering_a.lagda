% Ordering View
% Ambrus Kaposi
% 2011. 12. 01.

\begin{code}
{-# OPTIONS --no-termination-check #-}
module Ordering_a where
\end{code}


Import List
===========

\begin{code}
open import Data.Nat  using (ℕ; zero; suc; pred; _+_)
open import Data.Bool using (Bool; true; false; if_then_else_)
\end{code}


Ordering View
=============

\begin{code}
data Ordering : ℕ → ℕ → Set where
  less    : ∀ m k → Ordering m (suc (m + k))
  equal   : ∀ m   → Ordering m m
  greater : ∀ m k → Ordering (suc (m + k)) m
\end{code}

*Exercise:* `Ordering` is a view of `ℕ × ℕ`. Prove this by defining the view function:

\begin{code}
compare : ∀ m n → Ordering m n
compare zero    zero    = equal   zero
compare (suc m) zero    = greater zero m
compare zero    (suc n) = less    zero n
compare (suc m) (suc n) with compare m n
compare (suc .m)           (suc .(suc m + k)) | less    m k = less    (suc m) k
compare (suc .m)           (suc .m)           | equal   m   = equal   (suc m)
compare (suc .(suc m + k)) (suc .m)           | greater m k = greater (suc m) k
\end{code}

Compare this with the Haskell datatype `Ordering`:

    data Ordering = LT | EQ | GT

Example
=======

\begin{code}
_≤?_ : ℕ → ℕ → Bool
zero  ≤? _     = true
suc n ≤? suc m = n ≤? m
suc _ ≤? zero  = false
infix 4 _≤?_
\end{code}

We call this a *question*. `n ≤ m` is `false` or `true` depending on the value of `n` and `m`. Booleans do not carry information about *what* and *why*.

Example of losing information when using a boolean:

\begin{code}
plus : ℕ → ℕ → ℕ
plus x y = if x ≤? zero then y else suc (plus (pred x) y)
\end{code}

(We've also lost termination check.)

\begin{code}
plus' : ℕ → ℕ → ℕ
plus' x y with compare x zero
plus' .0        y | equal   .0    = y
plus' .(suc px) y | greater .0 px = plus' px y
\end{code}
