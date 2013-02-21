% Dependently Typed Functions


\begin{code}
module Functions.Dependent where
\end{code}


Dependently typed functions
===============

Dependently typed function:

`f : (x : A) → B`, where `B` may depend on `x`

*Example*  
Let `Fin n` be the set of natural numbers less than `n`.  
`a : (n : ℕ) → Fin n` is a sequence whose `n`th elem is in `Fin n`.

*Notes*


-   Polymorph functions like `(A : Set) → A → A` are also dependent functions.
-   Non-dependent functions like `A → B` are special `(x : A) → B` functions where `B`
    doesn't depend on `x`.
-   ∣`(x : A)→ B`∣ = ∏`x`∈`A` ∣`B`∣, for example  
    ∣`(n : Fin m)→ Fin (suc n)`∣ = (`m` + 1)!


