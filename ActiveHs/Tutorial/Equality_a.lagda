% Equality
% Ambrus Kaposi
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
| Exercise: equivalence relation
| ==============================
| 
| Prove that `_≡_` is an equivalence-relation:
| 
| \begin{code}
| refl'  : ∀ {A : Set} (a : A) → a ≡ a
| refl' a = refl --
| sym   : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
| sym refl = refl --
| trans : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
| trans refl refl = refl --
| \end{code}
| 
| Prove that every function is compatible with the equivalence relation (congruency):
| 
| \begin{code}
| cong : {A B : Set} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
| cong f refl = refl --
| \end{code}
| 
| 
| `List ⊤` ~ `ℕ`
| ======================
| 
| \begin{code}
| fromList : List ⊤ → ℕ
| fromList [] = zero
| fromList (x ∷ xs) = suc $ fromList xs
| 
| toList : ℕ → List ⊤
| toList zero = []
| toList (suc n) = tt ∷ toList n
| \end{code}
| 
| We should prove that `fromList` is a bijection and `toList` is the inverse and that they preserve the operations `_++_` and `_+_`. We will prove that it is a bijection after we learned [Sigma](Sigma_a.xml#how-to-express-bijection).
| 
| *Exercise*. Define the following functions:
| 
| \begin{code}
| fromPreserves++ : ∀ (a b : List ⊤) → fromList (a ++ b) ≡ fromList a + fromList b
| fromPreserves++ [] b = refl --
| fromPreserves++ (x ∷ xs) b = cong suc $ fromPreserves++ xs b --
| toPreserves+ : ∀ (a b : ℕ) → toList (a + b) ≡ toList a ++ toList b
| toPreserves+ zero    b = refl --
| toPreserves+ (suc n) b = cong (_∷_ tt) $ toPreserves+ n b --
| \end{code}
| 
| 

| 
| Properties of addition
| ================================
| 
| We'd like to prove that (`ℕ`, `_+_`) is a commutative monoid.
| 
| *Exercise*: define the following functions:
| 
| \begin{code}
| +-assoc        : ∀ a b c → a + (b + c) ≡ (a + b) + c -- hint: use cong
| +-assoc zero    b c = refl --
| +-assoc (suc a) b c = cong suc $ +-assoc a b c --
| +-left-identity  : ∀ a → 0 + a ≡ a
| +-left-identity a = refl --
| +-right-identity : ∀ a → a + 0 ≡ a
| +-right-identity zero    = refl --
| +-right-identity (suc n) = cong suc $ +-right-identity n --
| +-identity       : ∀ a → 0 + a ≡ a × a + 0 ≡ a
| +-identity a = +-left-identity a , +-right-identity a --
| \end{code}
| 
| Commutativity:
| 
| \begin{code}
| -- helper function:
| m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
| m+1+n≡1+m+n zero n = refl
| m+1+n≡1+m+n (suc m) n = cong suc $ m+1+n≡1+m+n m n
| 
| +-comm : ∀ a b → a + b ≡ b + a
| +-comm zero b = sym $ +-right-identity b
| +-comm (suc n) b = trans
|   (cong suc $ +-comm n b)
|   (sym $ m+1+n≡1+m+n b n)
| \end{code}
| 
| 
| Equational reasoning
| ====================
| 
| \begin{code}
| _≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
| x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z
| 
| infixr 2 _≡⟨_⟩_
| 
| _∎ : ∀ {A : Set} (x : A) → x ≡ x
| x ∎ = refl
| 
| infix  2 _∎
| \end{code}
| 
| Example:
| 
| \begin{code}
| +-comm' : (n m : ℕ) → n + m ≡ m + n
| +-comm' zero    n = sym (+-right-identity n)
| +-comm' (suc m) n =
|       suc m + n
|     ≡⟨ refl ⟩
|       suc (m + n)
|     ≡⟨ cong suc (+-comm' m n) ⟩
|       suc (n + m)
|     ≡⟨ sym (m+1+n≡1+m+n n m) ⟩
|       n + suc m
|     ∎
| \end{code}
| 
| 
| 
| Properties of `_*_`
| ==============================
| 
| We'd like to prove that (`ℕ`, `_*_`) is a commutative monoid.
| 
| We will need distributivity:
| 
| \begin{code}
| distribʳ-*-+ : ∀ a b c → (a + b) * c ≡ a * c + b * c
| distribʳ-*-+ zero b c = refl
| distribʳ-*-+ (suc a) b c =
|     c + (a + b) * c
|   ≡⟨ cong (λ x → c + x) $ distribʳ-*-+ a b c ⟩
|     c + (a * c + b * c)
|   ≡⟨ +-assoc c (a * c) (b * c) ⟩
|     c + a * c + b * c
|   ∎
| \end{code}
| 
| 
| Define the following functions:
| 
| \begin{code}
| *-assoc        : ∀ a b c → a * (b * c) ≡ (a * b) * c
| *-assoc zero b c = refl --
| *-assoc (suc a) b c = --
|     b * c + a * (b * c) --
|   ≡⟨  cong (λ x → (b * c) + x) $ *-assoc a b c ⟩ --
|     b * c + a * b * c --
|   ≡⟨ sym $ distribʳ-*-+ b (a * b) c ⟩ --
|     (b + a * b) * c --
|   ∎ --
| *-left-identity  : ∀ a → 1 * a ≡ a
| *-left-identity a = +-right-identity a --
| *-right-identity : ∀ a → a * 1 ≡ a
| *-right-identity zero    = refl --
| *-right-identity (suc n) = cong suc $ *-right-identity n --
| *-identity       : ∀ a → 1 * a ≡ a × a * 1 ≡ a --
| *-identity a = *-left-identity a , *-right-identity a --
| \end{code}
| 
| Commutativity:
| 
| \begin{code}
| -- helper functions:
| n*0≡0 : ∀ n → n * 0 ≡ 0
| n*0≡0 zero    = refl --
| n*0≡0 (suc n) = n*0≡0 n --
| *-suc : ∀ n m → n + n * m ≡ n * suc m
| *-suc zero m = refl --
| *-suc (suc n) m = cong suc $ --
|     n + (m + n * m) --
|   ≡⟨ +-assoc n m (n * m) ⟩ --
|     n + m + n * m --
|   ≡⟨ cong (λ x → x + n * m) $ +-comm n m  ⟩ --
|     m + n + n * m --
|   ≡⟨ sym $ +-assoc m n (n * m) ⟩ --
|     m + (n + n * m) --
|   ≡⟨ cong (λ x → m + x) $ *-suc n m ⟩ --
|     m + n * suc m --
|   ∎ --
|   -- hint: you will need steps like this: cong (λ x → n + x) ...
| 
| *-comm : ∀ m n → m * n ≡ n * m
| *-comm zero n = sym $ n*0≡0 n --
| *-comm (suc m) n =  --
|     n + m * n --
|   ≡⟨ cong (λ x → n + x) (*-comm m n) ⟩ --
|     n + n * m --
|   ≡⟨ *-suc n m ⟩ --
|     n * suc m --
|   ∎ --
| \end{code}
| 
| Browse and read the Agda standard libraries: [http://www.cse.chalmers.se/\~nad/listings/lib-0.5/](http://www.cse.chalmers.se/~nad/listings/lib-0.5/)
| 
| 
| Semiring solver
| ===============
| 
| \begin{code}
| module trySemiringSolver where
| 
| open import Data.Nat
| open import Data.Nat.Properties
| open SemiringSolver
| open import Relation.Binary.PropositionalEquality renaming (_≡_ to _≡-official_)
| 
| f : ∀ a b c → a + b * c + 1 ≡-official 1 + c * b + a
| f = solve 3 (λ a b c → a :+ b :* c :+ con 1 := con 1 :+ c :* b :+ a) refl
| \end{code}
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


