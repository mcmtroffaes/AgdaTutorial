% Even, Odd
% Ambrus Kaposi
% 2011. 10. 20.

\begin{code}
module Even_a where
\end{code}


Import List
===========

\begin{code}
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
\end{code}


`Even`, `Odd` predicates
=================

\begin{code}
data Even : ℕ → Set where
  z  : Even zero
  ss : {n : ℕ} → Even n → Even (suc (suc n))

data Odd : ℕ → Set where
  o  : Odd (suc zero)
  ss : {n : ℕ} → Odd n → Odd (suc (suc n))
\end{code}

*Exercise*: define these functions:

\begin{code}
0even : Even 0
0even = z --
5odd : Odd 5
5odd = ss (ss o) --
6even : Even 6
6even = ss (ss (ss z)) --
\end{code}



Exercises
=========

Show these simple properties:

\begin{code}
odd+1    : {n : ℕ} → Odd  n → Even (suc n)
odd+1 o      = ss z --
odd+1 (ss n) = ss (odd+1 n) --
even+1   : {n : ℕ} → Even n → Odd (suc n)
even+1 z      = o --
even+1 (ss n) = ss (even+1 n) --
odd+even : {n m : ℕ} → Odd  n → Even m → Odd (n + m)
odd+even o      m = even+1 m --
odd+even (ss n) m = ss (odd+even n m) --
odd+odd  : {n m : ℕ} → Odd  n → Odd  m → Even (n + m)
odd+odd o      m = odd+1 m --
odd+odd (ss n) m = ss (odd+odd n m) --
odd*even : {n m : ℕ} → Even n → Odd  m → Even (n * m)
odd*even z m = z --
odd*even (ss n) m = odd+odd m (odd+even m (odd*even n m)) --
\end{code}

Exercise
========

Give a simpler definition of even and odd (with fewer constructors).
