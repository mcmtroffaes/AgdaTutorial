% Data Modules

\begin{code}
module Modules.Data where
\end{code}

Data modules
============

Data declarations define modules which are
immediately opened:

\begin{code}
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

x₁ : ℕ
x₁ = ℕ.suc ℕ.zero

x₂ : ℕ
x₂ = suc zero
\end{code}


Constructor name disambiguation
===============================

Data modules are provided for constructor name disambiguation:

\begin{code}
data ℕ′ : Set where
  zero : ℕ′
  suc  : ℕ′ → ℕ′

const : {A B : Set} → A → B → A
const a b = a

y₁ : ℕ′
y₁ = const ℕ′.zero (ℕ.suc ℕ.zero)  -- constructor name disambiguation
\end{code}


Automatic constructor name disambiguation
===============================

Constructor names are disambiguated automatically
if it is possible by observing the *result type*
of the constructor:

\begin{code}
y₂ : ℕ′
y₂ = const zero (ℕ.suc zero)   -- automatic name disambiguation

-- y₃ : ℕ′
-- y₃ = const zero (suc zero)  -- ambiguous

-- y₄ : ℕ′
-- y₄ = const zero (suc ℕ.zero) -- this is still ambiguous for Agda!
\end{code}

Ambiguous parts are highlighted in yellow.

