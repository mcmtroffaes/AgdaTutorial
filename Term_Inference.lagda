% Term Inference and Implicit Arguments
% Péter Diviánszky
% 2013. 01.


Imports
=======

\begin{code}
module Term_Inference where

open import Data.Empty    using (⊥)
open import Data.Unit     using (⊤; tt)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Data.Nat      using (ℕ; zero; suc)
\end{code}


Term inference
===========

The Agda compiler tries to infer terms marked with underscore.  
If the choice of term is ambiguous, term inference fails. 

Examples:

\begin{code}
data Fin′ : ℕ → Set where
  zero : (n : _) → Fin′ (suc n)   -- ℕ is inferred
  suc  : (n : _) → Fin′ n → Fin′ (suc n)   -- ℕ is inferred

x : Fin′ 3
x = suc _ (zero _)   -- 2 and 1 are inferred
\end{code}

------------

If term inference fails we see yellow colour.


Implicit arguments
==========

Underscores can be hidden:  
Mark argument positions of constructors *implicit* with curly brackets.

\begin{code}
data Fin : ℕ → Set where
  zero : {n : _} → Fin (suc n)
  suc  : {n : _} → Fin n → Fin (suc n)
\end{code}

After this we have

\begin{code}
x′ : Fin 3
x′ = suc {_} (zero {_}) 
\end{code}

`{_}` can be deleted:

\begin{code}
x″ : Fin 3
x″ = suc zero
\end{code}

-------------------

Although `zero : Fin 1` and `zero : Fin 2`, `zero` does not have multiple different types;
the implicit arguments make the types unique.

<!--
| The definition yields the statements
|
| ~~~~~~~~~~~~~~~~~ 
| zero : Fin 1
| zero : Fin 2
| zero : Fin 3
| ...
| suc zero : Fin 2
| suc zero : Fin 3
| suc zero : Fin 4
| ...
| suc (suc zero) : Fin 3
| suc (suc zero) : Fin 4
| suc (suc zero) : Fin 5
| ...
| ...
| ~~~~~~~~~~~~~~~~~
| which can be rearranged as
| 
| ~~~~~~~~~~~~~~~~~ 
| zero : Fin 1
| 
| zero : Fin 2
| suc zero : Fin 2
| 
| zero : Fin 3
| suc zero : Fin 3
| suc (suc zero) : Fin 3
| 
| zero : Fin 4
| suc zero : Fin 4
| suc (suc zero) : Fin 4
| suc (suc (suc zero)) : Fin 4
| 
| ...
| ~~~~~~~~~~~~~~~~~
-->

Named and multiple implicit arguments
==========

TODO




Syntactic abbreviations
=======================

~~~~~~~~~~~ 
data Fin′ : ℕ → Set where
  zero : (n : _) → Fin′ (suc n)
  suc  : (n : _) → Fin′ n → Fin′ (suc n)

data Fin : ℕ → Set where
  zero : {n : _} → Fin (suc n)
  suc  : {n : _} → Fin n → Fin (suc n)
~~~~~~~~~~~

Variables with inferred types can be introduced by `∀`:

~~~~~~~~~~~ 
data Fin′ : ℕ → Set where
  zero : ∀ n → Fin′ (suc n)
  suc  : ∀ n → Fin′ n → Fin′ (suc n)

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)
~~~~~~~~~~~




