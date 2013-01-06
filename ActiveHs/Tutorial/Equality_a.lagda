% Parameters vs. indices
% Ambrus Kaposi & Peter Divianszky
% 2011. 10. 05.

\begin{code}
module Equality_a where
\end{code}


Import List
===========

\begin{code}
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)
\end{code}
| open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
| open import Data.List using (List; []; _∷_; _++_)
| open import Data.Unit using (⊤; tt)
| open import Data.Product using (_×_; _,_)
| open import Function using (_$_; _∘_)


Parameters vs. indices
======================

The *first* index can be turned into a new parameter if
each constructor has the same variable on the first index position
(in the result type).

**Example 1**

~~~~~~ {.haskell}
data _≤′_ : ℕ → ℕ → Set where
  ≤′-refl : {m : ℕ} →                       m ≤′ m
  ≤′-step : {m : ℕ} → {n : ℕ} →  m ≤′ n  →  m ≤′ suc n
~~~~~~

is similar to

~~~~~~ {.haskell}
data _≤′_ (m : ℕ) : ℕ → Set where
  ≤′-refl :                       m ≤′ m
  ≤′-step : {n : ℕ} →  m ≤′ n  →  m ≤′ suc n
~~~~~~


**Example 2**

~~~~~~ {.haskell}
data _≤″_ : ℕ → ℕ → Set where
  ≤+ : ∀ {m n k} → m + n ≡ k → m ≤″ k
~~~~~~

is similar to

~~~~~~ {.haskell}
data _≤″_ (m : ℕ) : ℕ → Set where
  ≤+ : ∀ {n k} → m + n ≡ k → m ≤″ k
~~~~~~

which is similar to

~~~~~~ {.haskell}
data _≤″_ (m : ℕ) (k : ℕ) : Set where
  ≤+ : ∀ {n} → m + n ≡ k → m ≤″ k
~~~~~~

**Design decision**

A parameter instead of an index is always a better choice

*   We state more about the structure of the set.*  
    In turn, the Agda compiler can infer more properties of the set.**
*   Cleaner syntax: each constructor has one parameter less.  

*********************

*The parameter can be fixed to get a simpler definition, for example

~~~~~~ {.haskell}
data 10≤′ : ℕ → Set where
  10≤′-refl :                       10≤′ 10
  10≤′-step : {n : ℕ} →  10≤′ n  →  10≤′ suc n
~~~~~~

was made from `_≤′_` with a simple substituion which is possible with `_≤_`.

**TODO: give examples.


Parameters vs. indices (2)
======================

The parameters of the set are present as implicit arguments in the constructors.

TODO 



| A simpler definition
| ====================
| 
| Motivation:
| 
| \begin{code}
| ≡₁-refl : (a : ℕ) → a ≡₁ a
| ≡₁-refl zero = zz
| ≡₁-refl (suc n) = ss (≡₁-refl n)
| \end{code}
| 
| Definition with reflexivity:
| 
| \begin{code}
| data _≡₂_ (a : ℕ) : ℕ → Set where
|   refl : a ≡₂ a
| 
| 
| infix 4 _≡₂_
| \end{code}
| 
| *Exercise*:
| 
| Create conversion functions between the two equalites:
| 
| \begin{code}
| cong₂ : ∀ {a b} (f : ℕ → ℕ) → a ≡₂ b → f a ≡₂ f b -- helper function
| cong₂ f refl = refl --
| 1→2 : ∀ {a b} → a ≡₁ b → a ≡₂ b
| 1→2 zz = refl --
| 1→2 (ss a≡₁b) = cong₂ suc $ 1→2 a≡₁b --
| 2→1 : ∀ a b → a ≡₂ b → a ≡₁ b
| 2→1 zero .0 refl = zz --
| 2→1 (suc n) .(suc n) refl = ss $ 2→1 n n refl --
| \end{code}


General equality: `_≡_`
================

\begin{code}
data  _≡_ {A : Set} (x : A) : A → Set  where
  refl : x ≡ x

infix 4 _≡_
\end{code}

yields

~~~~~~~~~~~~~~~~~ {.haskell}
refl {ℕ} {0} : 0 ≡ 0
refl {ℕ} {1} : 1 ≡ 1
refl {ℕ} {2} : 2 ≡ 2
...
~~~~~~~~~~~~~~~~~

so it represents equality!

| *Examples:*
| 
| Set           1st,      2nd, 3rd, ...
| ------------- --------- ---------------
| `0 ≡ 0` = {   `refl {0}` }
| `0 ≡ 1` = { }
| `0 ≡ 2` = { }
| ...                  
| `1 ≡ 0` = { } 
| `1 ≡ 1` = {   `refl {1}` }
| `1 ≡ 2` = { }
| ...                        
| `2 ≡ 0` = { } 
| `2 ≡ 1` = { }
| `2 ≡ 2` = {   `refl {2}` }
| ...           
| ...           ...     
| 
| 


`_∈_` proposition
===============

Another parametric definition:

\begin{code}
data _∈_ {A : Set}(x : A) : List A → Set where
  first : ∀ {xs} → x ∈ x ∷ xs
  later : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

infix 4 _∈_
\end{code}


Exercises
=========

*   Define `_⊆_ {A : Set} : List A → List A → Set`!
    *   Prove that `1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ []`!
    *   Prove that `1 ∷ 2 ∷ 3 ∷ [] ⊆ 1 ∷ 2 ∷ []` is false!
*   Define a permutation predicate!
*   Define a sort predicate!

\begin{code}
data _⊆_ {A : Set} : List A → List A → Set where --
    stop :                                              [] ⊆ [] --
    drop : ∀ {xs ys y} → xs ⊆ ys →       xs ⊆ (y ∷ ys) --
    keep : ∀ {xs ys x} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys) --

infix 4 _⊆_ --

e0 : 1 ∷ [] ⊆ 1 ∷ [] --
e0 = keep stop --
e1 : 1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ [] --
e1 =  keep (keep (drop stop)) --
\end{code}

***************

You can type `⊆` as `\sub=`.


