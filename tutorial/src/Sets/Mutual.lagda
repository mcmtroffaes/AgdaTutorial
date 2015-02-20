% Mutually Recursive Sets

\begin{code}
module Sets.Mutual where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
\end{code}


Mutual definitions
=========

To allow mutual definitions one should declare any set before using it:

\begin{code}
data L : Set
data M : Set

data L where
  nil : L
  _∷_ : ℕ → M → L

data M where
  _∷_ : Bool → L → M
\end{code}

Note that `: Set` is missing in the definitions of sets declared before.

*Exercise*: What are the elements of `L` and `M`?




Exercise
=========

*   Define trees where each node can have any finite number of children
    (0, 1, 2, ...).

Exercise
=========


Define a small grammar!*

-------

*highly underspecified exercise


