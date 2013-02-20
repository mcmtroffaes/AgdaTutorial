% Constant Definitions

Import List
===========

\begin{code}
module Constants where

open import Sets.Enumerated using (Bool; true; false)
open import Sets.Recursive using (ℕ; zero; suc)
\end{code}


Constant definitions
=======================

Definition of `nine` with the constructors `suc` and `zero`:

\begin{code}
nine : ℕ
nine = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
\end{code}

Definition of `ten` with the help of `nine`:

\begin{code}
ten : ℕ
ten = suc nine
\end{code}

The type signature is optional.


Normal form
=======================


