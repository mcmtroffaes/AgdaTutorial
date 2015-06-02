% Term Inference and Implicit Arguments
% Péter Diviánszky
% 2013. 01.


Import list
===========

\begin{code}
module Term_Inference where

open import Data.Empty    using (⊥)
open import Data.Unit     using (⊤; tt)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Data.Nat      using (ℕ; zero; suc)
\end{code}


Term inference
==============

The Agda compiler tries to infer terms marked with underscore.  If the choice
of term is ambiguous, the term inference will fail.

*Examples:*

\begin{code}
data Fin′ : ℕ → Set where
  zero : (n : _) → Fin′ (suc n)            -- ℕ is inferred
  suc  : (n : _) → Fin′ n → Fin′ (suc n)   -- ℕ is inferred again

x : Fin′ 3
x = suc _ (zero _)   -- 2 and 1 are inferred
\end{code}

------------

Term inference failure is marked with yellow colour.


Implicit arguments
==================

Underscores can be hidden by making arguments of constructors *implicit* with
curly brackets.

\begin{code}
data Fin : ℕ → Set where
  zero : {n : _} → Fin (suc n)
  suc  : {n : _} → Fin n → Fin (suc n)
\end{code}

After that, we obtain the following:

\begin{code}
x′ : Fin 3
x′ = suc {_} (zero {_})
\end{code}

And the `{_}`s can be now deleted:

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

There can be more implicit arguments, as the following definition
demonstrates:

\begin{code}
data T : ℕ → ℕ → ℕ → Set where
  c : {n m k : _} → T (suc n) (suc m) (suc k)

xt : T 1 2 3
xt = c
\end{code}

In addition to that, in case of multiple implicit arguments, some of their
actual values may be set by naming them.  For example:

\begin{code}
xt' : T 1 2 3
xt' = c {m = 1}
\end{code}

Syntactic abbreviations
=======================

Consider the following definitions again from above:

~~~~~~~~~~
data Fin′ : ℕ → Set where
  zero : (n : _) → Fin′ (suc n)
  suc  : (n : _) → Fin′ n → Fin′ (suc n)

data Fin : ℕ → Set where
  zero : {n : _} → Fin (suc n)
  suc  : {n : _} → Fin n → Fin (suc n)
~~~~~~~~~~~

There variables with inferred types can be introduced by the `∀` (universal
quantification) symbol, no matter if they are explicit or implicit:

~~~~~~~~~~~
data Fin′ : ℕ → Set where
  zero : ∀ n → Fin′ (suc n)
  suc  : ∀ n → Fin′ n → Fin′ (suc n)

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)
~~~~~~~~~~~
