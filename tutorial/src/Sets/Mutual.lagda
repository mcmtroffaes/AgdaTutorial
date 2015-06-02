% Mutually Recursive Sets

\begin{code}
module Sets.Mutual where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
\end{code}


Mutual definitions
=========

In order to allow mutual definitions, one should declare any `Set` before
using it.  Those are called "forward declarations" &mdash; they are not unique
to Agda.

Consider the following example for this:

\begin{code}
-- forward declarations
data L : Set
data M : Set

-- actual declarations
data L where
  nil : L
  _∷_ : ℕ → M → L

data M where
  _TT∷_ : Bool → L → M
\end{code}

Note that `: Set` is missing from the definitions of the forward-declared
sets.

Exercises
---------

#. What are the elements of `L` and `M`?

#. Define trees where each node can have arbitrary (finite) number of children
   (such as 0, 1, 2, and so on).

#. Define a language by the following grammar in Agda:

     $E \to B$  
     $E \to I$  
     $I \to I + I$  
     $I \to I - I$  
     $I \to I * I$  
     $I \to z$  
     $I \to s I$  
     $B \to t$  
     $B \to f$  
     $B \to E = E$  
     $B \to E ≠ E$  

#. As a constant, give an element of the language defined in the previous
   exercise that contains the application of every rule at least once.
