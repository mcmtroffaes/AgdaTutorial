% Subsets
% Péter Diviánszky
% 2011. 05. 03.

\begin{code}
module Subsets_a where
\end{code}


`Fin`: Family of Finite Sets
============

`Fin` has an *index* typed `ℕ`:

\begin{code}
data Fin : ℕ → Set where
  zero : (n : ℕ) →         Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)
\end{code}

If possible, it's better to use parameters instead of indexes.

Note that the index cannot be turned to be a parameter because
there is at least one constructor for which the result has a non-variable
parameter at the specific point.

Note that the type of `Fin` is `ℕ → Set`, not `Set → Set` as with GADTs.  

Elements of `Fin k`:

Set           1st,       2nd,             3rd,                   ...
------------- ---------- ---------------- ---------------------- ---
`Fin 0` = { }
`Fin 1` = {   `zero 0` }  
`Fin 2` = {   `zero 1`;  `suc (zero 0)` }
`Fin 3` = {   `zero 2`;  `suc (zero 1)`;  `suc (suc (zero 0))` }
...           ...        ...              ...                    ...

`⊥` ~ `Fin 0`  
`⊤` ~ `Fin 1`  
`Bool` ~ `Fin 2` 

*********************


Indexed sets are the first subset of inductive families discussed here which cannot be defined in Haskell.


`Vec`: Vectors (Lists with Known Size)
======================================

`Vec` has a parameter and an index:

\begin{code}
data Vec (A : Set) : ℕ → Set where
  []  :                         Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
\end{code}


*Example:*  
Family of vectors of natural numbers:

Set           1st,       2nd,                       3rd,                   ...
------------- ---------- -------------------------- ---------------------- ---
`Vec ℕ 0` = { `[]` }
`Vec ℕ 1` = {            `0 ∷ []`; `13 ∷ []`; ... }
`Vec ℕ 2` = {                                       `3 ∷ 13 ∷ []`; ... }
...           ...        ...                        ...                    ...






`Σ`: Dependent Pair
==============

The most well-known set with dependent constructor parameters is the dependent pair:

\begin{code}
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B
\end{code}

Dependent pair is a very powerful tool:

-   `Σ A P` is the subset of `A` given a predicate `P` on `A`.
-   Existential quantification is defined with `Σ`.
-   `A × B` ~ `Σ A (const B)`
-   `A ⊎ B` ~ `Σ Bool (λ b → if b then A else B)`
-   `Σ Set id` ~ `Dynamic`
-   `Σ` sums a family of types:  
    `List A` ~ `Σ ℕ (Vec A)`.

*Concrete examples:*

Elements of `Σ ℕ Fin`:

    1 , zero 0
    2 , zero 1
    2 , suc (zero 0)
    3 , zero 2
    3 , suc (zero 1)
    3 , suc (suc (zero 0))
    ... 

`Fin n` ~ `Σ ℕ (λ k → suc k ≤ n)`
`Even n` ~ `Σ ℕ (λ k → n ≡ k * 2)`

We will discuss the `const`, `id`, `if_then_else_` functions and the λ-notation later.



