% Equality
% Ambrus Kaposi
% 2011. 10. 05.

\begin{code}
module Equality_a where
\end{code}


Import List
===========

\begin{code}
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Function using (_$_; _∘_)
\end{code}


Equality on `ℕ`
===============

\begin{code}
data _≡₁_ : ℕ → ℕ → Set where
  zz : zero ≡₁ zero
  ss : {m n : ℕ} → m ≡₁ n → suc m ≡₁ suc n

infix 4 _≡₁_
\end{code}

*Interpretation*:

\begin{code}
zz         ∈ zero ≡₁ zero
ss zz      ∈ suc zero ≡₁ suc zero
ss (ss zz) ∈ suc (suc zero) ≡₁ suc (suc zero)
...
\end{code}

This is not isomorphic to ℕ.

*Exercises:*

Define the symmetry and transitivity of `_≡₁_`:

\begin{code}
≡₁-sym : ∀ {n m} → n ≡₁ m → m ≡₁ n
| ≡₁-sym zz = zz
| ≡₁-sym (ss y) = ss (≡₁-sym y)
≡₁-trans : ∀ a b c → a ≡₁ b → b ≡₁ c → a ≡₁ c
| ≡₁-trans .0 .0 c zz b≡c = b≡c
| ≡₁-trans .(suc a) .(suc b) .(suc c) (ss {a} {b} a≡b) (ss {.b} {c} b≡c) = ss $ ≡₁-trans a b c a≡b b≡c
-- (reflexivity will be defined on next slide)
\end{code}

Now we can define the antisymmetric property of `_≤_`:

\begin{code}
antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡₁ n
| antisym z≤n z≤n = zz
| antisym (s≤s m≤n) (s≤s n≤m) = ss $ antisym m≤n n≤m
\end{code}


A simpler definition
====================

Motivation:

\begin{code}
≡₁-refl : (a : ℕ) → a ≡₁ a
≡₁-refl zero = zz
≡₁-refl (suc n) = ss (≡₁-refl n)
\end{code}

Definition with reflexivity:

\begin{code}
data _≡₂_ (a : ℕ) : ℕ → Set where
  refl : a ≡₂ a

infix 4 _≡₂_
\end{code}

*Exercise*:

Create conversion functions between the two equalites:

\begin{code}
cong₂ : ∀ {a b} (f : ℕ → ℕ) → a ≡₂ b → f a ≡₂ f b -- helper function
| cong₂ f refl = refl
1→2 : ∀ {a b} → a ≡₁ b → a ≡₂ b
| 1→2 zz = refl
| 1→2 (ss a≡₁b) = cong₂ suc $ 1→2 a≡₁b
2→1 : ∀ a b → a ≡₂ b → a ≡₁ b
| 2→1 zero .0 refl = zz
| 2→1 (suc n) .(suc n) refl = ss $ 2→1 n n refl
\end{code}


General Equality: `_≡_`
================

\begin{code}
data  _≡_ {A : Set} (x : A) : A → Set  where
  refl : x ≡ x

infix 4 _≡_
\end{code}

*Examples:*

Set           1st,      2nd, 3rd, ...
------------- --------- ---------------
`0 ≡ 0` = {   `refl {0}` }
`0 ≡ 1` = { }
`0 ≡ 2` = { }
...                  
`1 ≡ 0` = { } 
`1 ≡ 1` = {   `refl {1}` }
`1 ≡ 2` = { }
...                        
`2 ≡ 0` = { } 
`2 ≡ 1` = { }
`2 ≡ 2` = {   `refl {2}` }
...           
...           ...     


Exercise: equivalence relation
==============================

Prove that `_≡_` is an equivalence-relation:

\begin{code}
refl'  : ∀ {A : Set} (a : A) → a ≡ a
| refl' a = refl
sym   : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
| sym refl = refl
trans : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
| trans refl refl = refl
\end{code}

Prove that every function is compatible with the equivalence relation (congruency):

\begin{code}
cong : {A B : Set} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
| cong f refl = refl
\end{code}


`List ⊤` ~ `ℕ`
======================

\begin{code}
fromList : List ⊤ → ℕ
fromList [] = zero
fromList (x ∷ xs) = suc $ fromList xs

toList : ℕ → List ⊤
toList zero = []
toList (suc n) = tt ∷ toList n
\end{code}

We should prove that `fromList` is a bijection and `toList` is the inverse and that they preserve the operations `_++_` and `_+_`. We will prove that it is a bijection after we learned [Sigma](Sigma_a.xml#how-to-express-bijection).

*Exercise*. Define the following functions:

\begin{code}
fromPreserves++ : ∀ (a b : List ⊤) → fromList (a ++ b) ≡ fromList a + fromList b
| fromPreserves++ [] b = refl
| fromPreserves++ (x ∷ xs) b = cong suc $ fromPreserves++ xs b
toPreserves+ : ∀ (a b : ℕ) → toList (a + b) ≡ toList a ++ toList b
| toPreserves+ zero    b = refl
| toPreserves+ (suc n) b = cong (_∷_ tt) $ toPreserves+ n b
\end{code}



Properties of addition
================================

We'd like to prove that (`ℕ`, `_+_`) is a commutative monoid.

*Exercise*: define the following functions:

\begin{code}
+-assoc        : ∀ a b c → a + (b + c) ≡ (a + b) + c -- hint: use cong
| +-assoc zero    b c = refl
| +-assoc (suc a) b c = cong suc $ +-assoc a b c
left-identity  : ∀ a → 0 + a ≡ a
| left-identity a = refl
right-identity : ∀ a → a + 0 ≡ a
| right-identity zero    = refl
| right-identity (suc n) = cong suc $ right-identity n
identity       : ∀ a → 0 + a ≡ a × a + 0 ≡ a
| identity a = left-identity a , right-identity a
\end{code}

Commutativity:

\begin{code}
-- helper function:
m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero n = refl
m+1+n≡1+m+n (suc m) n = cong suc $ m+1+n≡1+m+n m n

+-comm : ∀ a b → a + b ≡ b + a
+-comm zero b = sym $ right-identity b
+-comm (suc n) b = trans
  (cong suc $ +-comm n b)
  (sym $ m+1+n≡1+m+n b n)
\end{code}


Equational reasoning
====================

\begin{code}
_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

infixr 2 _≡⟨_⟩_

_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = refl

infix  2 _∎
\end{code}

Example:

\begin{code}
+-comm' : (n m : ℕ) → n + m ≡ m + n
+-comm' zero    n = sym (right-identity n)
+-comm' (suc m) n =
      suc m + n
    ≡⟨ refl ⟩
      suc (m + n)
    ≡⟨ cong suc (+-comm' m n) ⟩
      suc (n + m)
    ≡⟨ sym (m+1+n≡1+m+n n m) ⟩
      n + suc m
    ∎
\end{code}



Properties of `_*_`
==============================

We'd like to prove that (`ℕ`, `_*_`) is a commutative monoid.

We will need distributivity:

\begin{code}
distribʳ-*-+ : ∀ a b c → (a + b) * c ≡ a * c + b * c
distribʳ-*-+ zero b c = refl
distribʳ-*-+ (suc a) b c =
    c + (a + b) * c
  ≡⟨ cong (λ x → c + x) $ distribʳ-*-+ a b c ⟩
    c + (a * c + b * c)
  ≡⟨ +-assoc c (a * c) (b * c) ⟩
    c + a * c + b * c
  ∎
\end{code}


Define the following functions:

\begin{code}
*-assoc        : ∀ a b c → a * (b * c) ≡ (a * b) * c
| *-assoc zero b c = refl
| *-assoc (suc a) b c =
|     b * c + a * (b * c)
|   ≡⟨  cong (λ x → (b * c) + x) $ *-assoc a b c ⟩
|     b * c + a * b * c
|   ≡⟨ sym $ distribʳ-*-+ b (a * b) c ⟩
|     (b + a * b) * c
|   ∎
left-identity  : ∀ a → 1 * a ≡ a
right-identity : ∀ a → a * 1 ≡ a
identity       : ∀ a → 1 * a ≡ a × a * 1 ≡ a
\end{code}

Commutativity:

\begin{code}
-- helper functions:
n*0≡0 : ∀ n → n * 0 ≡ 0
| n*0≡0 zero    = refl
| n*0≡0 (suc n) = n*0≡0 n
*-suc : ∀ n m → n + n * m ≡ n * suc m
| *-suc zero m = refl
| *-suc (suc n) m = cong suc $
|     n + (m + n * m)
|   ≡⟨ +-assoc n m (n * m) ⟩
|     n + m + n * m
|   ≡⟨ cong (λ x → x + n * m) $ +-comm n m  ⟩
|     m + n + n * m
|   ≡⟨ sym $ +-assoc m n (n * m) ⟩
|     m + (n + n * m)
|   ≡⟨ cong (λ x → m + x) $ *-suc n m ⟩
|     m + n * suc m
|   ∎
  -- hint: you will need steps like this: cong (λ x → n + x) ...

*-comm : ∀ m n → m * n ≡ n * m
| *-comm zero n = sym $ n*0≡0 n
| *-comm (suc m) n = 
|     n + m * n
|   ≡⟨ cong (λ x → n + x) (*-comm m n) ⟩
|     n + n * m
|   ≡⟨ *-suc n m ⟩
|     n * suc m
|   ∎
\end{code}

Browse and read the Agda standard libraries: [http://www.cse.chalmers.se/\~nad/listings/lib-0.5/](http://www.cse.chalmers.se/~nad/listings/lib-0.5/)


Semiring solver
===============

\begin{code}
module trySemiringSolver where

open import Data.Nat
open import Data.Nat.Properties
open SemiringSolver
open import Relation.Binary.PropositionalEquality

f : ∀ a b c → a + b * c + 1 ≡ 1 + c * b + a
f = solve 3 (λ a b c → a :+ b :* c :+ con 1 := con 1 :+ c :* b :+ a) refl
\end{code}



Exercise
========

Explore the elements of the following set:

\begin{code}
data _≠_ : ℕ → ℕ → Set where
  z≠s : {n : ℕ}   →          zero ≠ suc n
  s≠z : {n : ℕ}   →         suc n ≠ zero
  s≠s : {m n : ℕ} → m ≠ n → suc m ≠ suc n
\end{code}
