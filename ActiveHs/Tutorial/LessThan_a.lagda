% ≤ predicate on ℕ
% Péter Diviánszky and Ambrus Kaposi
% 2011. 05. 03.


Imports
========

\begin{code}
module LessThan_a where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
\end{code}
| open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
| open import Function using (flip; _$_; _∘_)


`_≤_`: Less-or-equal predicate
==========

We wish to give a definition which
yields the infinite set of statements


| ~~~~~~~~~~~~~~~~~ {.haskell}
| zero ≤ zero
| zero ≤ suc zero
| zero ≤ suc (suc zero)
| ...
| suc zero ≤ suc zero
| suc zero ≤ suc (suc zero)
| suc zero ≤ suc (suc (suc zero))
| ...
| suc (suc zero) ≤ suc (suc zero)
| suc (suc zero) ≤ suc (suc (suc zero))
| suc (suc zero) ≤ suc (suc (suc (suc zero)))
| ...
| ...
| ~~~~~~~~~~~~~~~~~

~~~~~~~~~~~~~~~~~ {.haskell}
0 ≤ 0
0 ≤ 1,  1 ≤ 1
0 ≤ 2,  1 ≤ 2,  2 ≤ 2
0 ≤ 3,  1 ≤ 3,  2 ≤ 3,  3 ≤ 3
...                             ...
~~~~~~~~~~~~~~~~~



The outline of the solution:

~~~~~~~~~~~~~~~~~ {.haskell}
(n : ℕ)                     zero  ≤ n         -- yields the first column of statements
(n : ℕ) (m : ℕ)   n ≤ m  →  suc n ≤ suc m     -- yields the successive columns of statements
~~~~~~~~~~~~~~~~~

Technical details of the solution:

*   We define the *set* `n ≤ m` for each `n : ℕ` and `m : ℕ`.  
    (`1 ≤ 0` is a valid set too.)
*   The set `n ≤ m` will be non-empty iff `n` ≤ `m`.  
    (`0 ≤ 1` is non-empty, `1 ≤ 0` is empty.)

*********************************

The idea to represent true statements with non-empty sets and false statements with
empty sets turns out to be extremely useful as the examples will show.


Defintion of `_≤_`
==========

`_≤_` is an *indexed* set with two natural number indices and with two constructors:

\begin{code}
data  _≤_ : ℕ → ℕ → Set where
  z≤n : (n : ℕ) →                       zero  ≤ n
  s≤s : (m : ℕ) → (n : ℕ) →   m ≤ n  →  suc m ≤ suc n

infix 4 _≤_
\end{code}

which yields the statements


| ~~~~~~~~~~~~~~~~~ {.haskell}
| z≤n zero : zero ≤ zero
| z≤n (suc zero) : zero ≤ suc zero
| z≤n (suc (suc zero)) : zero ≤ suc (suc zero)
| ...
| s≤s zero zero (z≤n zero) : suc zero ≤ suc zero
| s≤s zero (suc zero) (z≤n (suc zero)) : suc zero ≤ suc (suc zero)
| s≤s zero (suc (suc zero)) (z≤n (suc (suc zero))) : suc zero ≤ suc (suc (suc zero))
| ...
| s≤s (suc zero) (suc zero) (s≤s zero zero (z≤n zero)) : suc (suc zero) ≤ suc (suc zero)
| s≤s (suc zero) (suc (suc zero)) (s≤s zero (suc zero) (z≤n (suc zero))) : suc (suc zero) ≤ suc (suc (suc zero))
| s≤s (suc zero) (suc (suc (suc zero))) (s≤s zero (suc (suc zero)) (z≤n (suc (suc zero)))) : suc (suc zero) ≤|  suc (suc (suc (suc zero)))
| ...
| ...
| ~~~~~~~~~~~~~~~~~
| 
| The same with decimal literals:

~~~~~~~~~~~~~~~~~ {.haskell}
z≤n 0 : 0 ≤ 0
z≤n 1 : 0 ≤ 1
z≤n 2 : 0 ≤ 2
...
s≤s 0 0 (z≤n 0) : 1 ≤ 1
s≤s 0 1 (z≤n 1) : 1 ≤ 2
s≤s 0 2 (z≤n 2) : 1 ≤ 3
...
s≤s 1 1 (s≤s 0 0 (z≤n 0)) : 2 ≤ 2
s≤s 1 2 (s≤s 0 1 (z≤n 1)) : 2 ≤ 3
s≤s 1 3 (s≤s 0 2 (z≤n 2)) : 2 ≤ 4
...
...
~~~~~~~~~~~~~~~~~

Notes

*   The actual structure of the elements of `m ≤ n` are not as important as the fact that these elements exist.
*   `1 ≤ 0` is also a valid expression which denotes an empty set.
*   `s≤s 1 0 (z≤n 0)` would be an invalid expression. (*Exercise*: why?)


Proving non-emptiness
========

We can prove that a set is non-empty by giving an element  
(remember the syntax of constant definition):

\begin{code}
0≤1 : 1 ≤ 10
0≤1 = s≤s 0 9 (z≤n 9)
\end{code}

*Exercise:* Prove that 3 ≤ 7!


Proving emptiness
================

How can we prove that a set like `7 ≤ 3` is empty?

1.  If `7 ≤ 3` would be non-empty, all its elements would look like `s≤s 6 2 x` where `x : 6 ≤ 2`.
    *   `z≤n n` yields an element in `0 ≤ n` and `0` ≠ `7`.
1.  If `6 ≤ 2` would be non-empty, all its elements would look like `s≤s 5 1 x` where `x : 5 ≤ 1`.
    *   `z≤n n` yields an element in `0 ≤ n` and `0` ≠ `6`.
1.  If `5 ≤ 1` would be non-empty, all its elements would look like `s≤s 4 0 x` where `x : 4 ≤ 0`.
    *   `z≤n n` yields an element in `0 ≤ n` and `0` ≠ `5`.
1.  `4 ≤ 0` is empty.
    *   `z≤n n` yields an element in `0 ≤ n` and `0` ≠ `4`.
    *   `s≤s m n` yields an element in `suc m ≤ suc n` and `suc n` ≠ `0`.

Although we will discuss all the details later here we have a look at
how can this chain of inference be given in Agda:*

\begin{code}
7≰3 : 7 ≤ 3 → ⊥
7≰3 (s≤s .6 .2 (s≤s .5 .1 (s≤s .4 .0 ())))
\end{code}

*   In emptiness proofs, values which are unambiguous should be dotted.**
*   `()` denotes a value in a trivially empty set.

*Exercise:* prove that `4 ≤ 2` is empty!

We can use an emptiness proofs in another emptiness proof:

\begin{code}
8≰4 : 8 ≤ 4 → ⊥
8≰4 (s≤s .7 .3 x) = 7≰3 x
\end{code}

*   `x` is an arbitrary variable name.

*Question:* Guess what kind of code can be generated from emptiness proofs!


***************************

*`7 ≤ 3 → ⊥` denotes a function from `7 ≤ 3` to `⊥` so we prove that
`7 ≤ 3` is empty by giving a function which maps `7 ≤ 3` to a trivially empty set.  
During the function definition we show that `7 ≤ 3` has no element so the function is defined.  
We discuss functions in detail later.

**Not just in emptiness proofs, this rule holds for patterns in general. We discuss patterns in detail later.



Exercises
=========

*   Define an indexed set `_isDoubleOf_ : ℕ → ℕ → Set` such that `m isDoubleOf n` is non-empty iff `m` is the double of `n`!
    *   Prove that `8 isDoubleOf 4` is non-empty!
    *   Prove that `9 isDoubleOf 4` is empty!
*   Define an indexed set `Odd : ℕ → Set` such that `odd n` is non-empty iff `n` is odd!
    *   Prove that `Odd 8` is non-empty!
    *   Prove that `Odd 9` is empty!
*   Define `Even : ℕ → Set` and `Odd : ℕ → Set` mutually!
*   Define equlity `_≡_ : ℕ → ℕ → Set`!
*   Define non-equlity `_≠_ : ℕ → ℕ → Set`!


| Equality on `ℕ`
| ===============

\begin{code}
data _≡₁_ : ℕ → ℕ → Set where --
  zz : zero ≡₁ zero --
  ss : {m n : ℕ} → m ≡₁ n → suc m ≡₁ suc n --

infix 4 _≡₁_ --
\end{code}

| yields
| 
| ~~~~~~~~~~~~~~~~~ {.haskell}
| zz         : 0 ≡₁ 0
| ss zz      : 1 ≡₁ 1
| ss (ss zz) : 2 ≡₁ 2
| ...
| ~~~~~~~~~~~~~~~~~

| This is not isomorphic to ℕ.
| 
| *Exercises:*
| 
| Define the symmetry and transitivity of `_≡₁_`:
| 
| \begin{code}
| ≡₁-sym : ∀ {n m} → n ≡₁ m → m ≡₁ n
| ≡₁-sym zz = zz --
| ≡₁-sym (ss y) = ss (≡₁-sym y) --
| ≡₁-trans : ∀ a b c → a ≡₁ b → b ≡₁ c → a ≡₁ c
| ≡₁-trans .0 .0 c zz b≡c = b≡c --
| ≡₁-trans .(suc a) .(suc b) .(suc c) (ss {a} {b} a≡b) (ss {.b} {c} b≡c) = ss $ ≡₁-trans a b c a≡b b≡c --
| -- (reflexivity will be defined on next slide)
| \end{code}
| 
| Now we can define the antisymmetric property of `_≤_`:
| 
| \begin{code}
| antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡₁ n
| antisym z≤n z≤n = zz --
| antisym (s≤s m≤n) (s≤s n≤m) = ss $ antisym m≤n n≤m --
| \end{code}

\begin{code}
data _≠_ : ℕ → ℕ → Set where --
  z≠s : {n : ℕ}   →          zero ≠ suc n --
  s≠z : {n : ℕ}   →         suc n ≠ zero --
  s≠s : {m n : ℕ} → m ≠ n → suc m ≠ suc n --

\end{code}


\begin{code}
data _isDoubleOf_ : ℕ → ℕ → Set where  --
  z : zero isDoubleOf zero --
  s : (m n : ℕ) → m isDoubleOf n → suc (suc m) isDoubleOf suc n --

8isDoubleOf4 : 8 isDoubleOf 4 --
8isDoubleOf4 = s 6 3 (s 4 2 (s 2 1 (s 0 0 z))) --

9isDoubleOf4 : 9 isDoubleOf 4 → ⊥ --
9isDoubleOf4 (s .7 .3 (s .5 .2 (s .3 .1 (s .1 .0 ()))))  --
\end{code}


Implicit parameters
==========

We are not interested in the parameters of constructors which usually *can be inferred*.  
Agda makes possible to hide these parameters (note the curly brackets):

~~~~~~~~~~~ {.haskell}
data  _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} →                       zero  ≤ n
  s≤s : {m : ℕ} → {n : ℕ} →   m ≤ n  →  suc m ≤ suc n

infix 4 _≤_
~~~~~~~~~~~

which yields the statements

~~~~~~~~~~~~~~~~~ {.haskell}
z≤n : 0 ≤ 0
z≤n : 0 ≤ 1
z≤n : 0 ≤ 2
...
s≤s z≤n : 1 ≤ 1
s≤s z≤n : 1 ≤ 2
s≤s z≤n : 1 ≤ 3
...
s≤s (s≤s z≤n) : 2 ≤ 2
s≤s (s≤s z≤n) : 2 ≤ 3
s≤s (s≤s z≤n) : 2 ≤ 4
...
...
~~~~~~~~~~~~~~~~~

Note that `z≤n` is different in `z≤n : 0 ≤ 0` and in `z≤n : 0 ≤ 1` because of the hidden parameter!



| `m ≤ n` has exactly one element if `m` less than or equal to `n`:
| 
| Set           1st,      2nd,            3rd,                   ...
| ------------- --------- --------------- ---------------------- ---
| `0 ≤ 0` = {   `z≤n 0` }
| `0 ≤ 1` = {   `z≤n 1` }
| `0 ≤ 2` = {   `z≤n 2` }
| ...           ...       
| `1 ≤ 0` = { } 
| `1 ≤ 1` = {             `s≤s (z≤n 0)` }
| `1 ≤ 2` = {             `s≤s (z≤n 1)` }
| ...                     ...             
| `2 ≤ 0` = { } 
| `2 ≤ 1` = { }
| `2 ≤ 2` = {                             `s≤s (s≤s (z≤n 1))` }
| ...                                     ...                    
| ...           ...       ...             ...                    ...
| 
| 
| `z≤n` and `s≤s` can be seen as the generators of the sets.
| 
| 
| `_≤?_ : ℕ → ℕ → Bool` is a *question*. `n ≤ m` is `false` or `true`
| depending on the value of `n` and `m`.
| 
| `_≤_ : ℕ → ℕ → Set` is a statement or *assertion*. If `q : n ≤ m` then
| n ≤ m.
| 
| 
| Exercise
| ==========
| 
| Define the following convenience functions:
| 
| \begin{code}
| _<_ : ℕ → ℕ → Set
| a < b = suc a ≤ b --
| _≥_ : ℕ → ℕ → Set
| _≥_ = flip _≤_ --
| _>_ : ℕ → ℕ → Set
| _>_ = flip _<_ --
| 
| infix 4 _<_ _≥_ _>_
| \end{code}
| 
| 
| 
| 
| Proofs
| ======
| 
| Define the following functions (prove these properties):
| 
| \begin{code}
| ≤-refl       : ∀ {n} → n ≤ n
| ≤-refl {zero}  = z≤n zero --
| ≤-refl {suc n} = s≤s $ ≤-refl {n} --
| ≤-trans      : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
| ≤-trans (z≤n _)   n≤o       = z≤n _ --
| ≤-trans (s≤s m≤n) (s≤s n≤o) = s≤s $ ≤-trans m≤n n≤o --
| -- antisym   : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
| --   (we will only define this after we have defined equality)
| total        : ∀ m n → m ≤ n ⊎ n ≤ m -- hint: use [_,_]′
| total zero    _       = inj₁ $ z≤n _ --
| total _       zero    = inj₂ $ z≤n _ --
| total (suc m) (suc n)  --
|    = [_,_]′ --
|        (λ m≤n → inj₁ (s≤s m≤n)) --
|        (λ n≤m → inj₂ (s≤s n≤m)) --
|        (total m n) --
| \end{code}
| 
| From the 4 above properties follows that `_≤_` is a total order on `ℕ`. (We can look at `_≤_` as a relation over `ℕ`.)
| 
| \begin{code}
| ≤-pred  : ∀ {m n} → suc m ≤ suc n → m ≤ n
| ≤-pred (s≤s m≤n) = m≤n --
| ≤-mono  : ∀ {m n k} → n ≤ m → k + n ≤ k + m
| ≤-mono {k = zero}  n≤m = n≤m --
| ≤-mono {k = suc k} n≤m = s≤s $ ≤-mono {k = k} n≤m --
| 
| \end{code}



Alternative representation
========

\begin{code}
data _≤′_ : ℕ → ℕ → Set where
  ≤′-refl : {m : ℕ} →                       m ≤′ m
  ≤′-step : {m : ℕ} → {n : ℕ} →  m ≤′ n  →  m ≤′ suc n

infix 4 _≤′_
\end{code}

yields

~~~~~~~~~~~~~~~~~ {.haskell}
≤′-refl : 0 ≤ 0
≤′-step ≤′-refl : 0 ≤ 1
≤′-step (≤′-step ≤′-refl) : 0 ≤ 2
...
≤′-refl : 1 ≤ 1
≤′-step ≤′-refl : 1 ≤ 2
≤′-step (≤′-step ≤′-refl) : 1 ≤ 3
...
≤′-refl : 2 ≤ 2
≤′-step ≤′-refl : 2 ≤ 3
≤′-step (≤′-step ≤′-refl) : 2 ≤ 4
...
...
~~~~~~~~~~~~~~~~~

As with `ℕ` and `ℕ₂`,

*   the structure of the `m ≤ n` and `m ≤′ n` set elements are different
*   different representations are good for different tasks  


| Alternative Definition
| ========
| 
| \begin{code}
| data _≤′_ (m : ℕ) : ℕ → Set where
|   ≤′-refl :                    m ≤′ m
|   ≤′-step : {n : ℕ} → m ≤′ n → m ≤′ suc n
| 
| infix 4 _≤′_
| \end{code}
| 
| Other alternative definition:
| 
| \begin{code}
| data  _≤″_ : ℕ → ℕ → Set  where
|    diff : (i j : ℕ) → i ≤″ j + i
| 
| infix 4 _≤″_
| \end{code}
| 
| *Exercise:*
| 
| Explore the elements of sets `_≤′_` and `_≤″_`!
| 
| 
| Rationale behind different definitions
| ======================================
| 
| *Exercise:*
| 
| Define the following functions:
| 
| \begin{code}
| 3≤5  : 3 ≤ 5
| 3≤5 = s≤s (s≤s (s≤s (z≤n (suc (suc zero))))) --
| 3≤′5 : 3 ≤′ 5
| 3≤′5 = ≤′-step (≤′-step ≤′-refl) --
| 3≤″5 : 3 ≤″ 5
| 3≤″5 = diff (suc (suc (suc zero))) (suc (suc zero)) --
| 
| 4≤4  : 4 ≤ 4
| 4≤4 = s≤s (s≤s (s≤s (s≤s (z≤n zero)))) --
| 4≤′4 : 4 ≤′ 4
| 4≤′4 = ≤′-refl --
| 4≤″4 : 4 ≤″ 4
| 4≤″4 = diff (suc (suc (suc (suc zero)))) zero --
| \end{code}
| 
| 
| Define safe substraction:
| 
| \begin{code}
| _∸_if_ : (a b : ℕ) → b ≤ a → ℕ
| zero ∸ .0     if z≤n .0       = 0 --
| suc a ∸ zero  if z≤n .(suc a) = suc a --
| suc a ∸ suc b if s≤s p        = a ∸ b if p --
| \end{code}
| 
| Let's define it for the third version:
| 
| \begin{code}
| _∸_if″_ : (a b : ℕ) → b ≤″ a → ℕ
| .(j + b) ∸ b if″ diff .b j = j --
| \end{code}
| 
| 
| 
| Exercises
| =============
| 
| Define the following (helper and) conversion functions:
| 
| \begin{code}
| ≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n
| ≤-step (z≤n _)   = z≤n (suc _) --
| ≤-step (s≤s m≤n) = s≤s (≤-step m≤n) --
| ≤′⇒≤ : ∀ {a b} → a ≤′ b → a ≤ b
| ≤′⇒≤ ≤′-refl        = ≤-refl --
| ≤′⇒≤ (≤′-step m≤′n) = ≤-step $ ≤′⇒≤ m≤′n --
| 
| z≤′n : ∀ {n} → zero ≤′ n
| z≤′n {zero}  = ≤′-refl --
| z≤′n {suc n} = ≤′-step z≤′n --
| s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
| s≤′s ≤′-refl        = ≤′-refl --
| s≤′s (≤′-step m≤′n) = ≤′-step (s≤′s m≤′n) --
| ≤⇒≤′ : ∀ {a b} → a ≤ b → a ≤′ b
| ≤⇒≤′ (z≤n _)   = z≤′n --
| ≤⇒≤′ (s≤s a≤b) = s≤′s $ ≤⇒≤′ a≤b --
| \end{code}


Syntactic abbreviations
=======================

All code on this slide is valid.

Original definition:

~~~~~~~~~~~ {.haskell}
data  _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} →                       zero  ≤ n
  s≤s : {m : ℕ} → {n : ℕ} →   m ≤ n  →  suc m ≤ suc n
~~~~~~~~~~~

The arrow between typed variables are not needed (also in case of round parenthesis):

~~~~~~~~~~~ {.haskell}
data  _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} →                     zero  ≤ n
  s≤s : {m : ℕ} {n : ℕ} →   m ≤ n  →  suc m ≤ suc n
~~~~~~~~~~~

Typed variables with the same type can be contracted (also in case of round parenthesis):

~~~~~~~~~~~ {.haskell}
data  _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} →               zero  ≤ n
  s≤s : {m n : ℕ} →   m ≤ n  →  suc m ≤ suc n
~~~~~~~~~~~

Inferable expressions can be replaced by an underscore:

~~~~~~~~~~~ {.haskell}
data  _≤_ : ℕ → ℕ → Set where
  z≤n : {n : _} →               zero  ≤ n
  s≤s : {m n : _} →   m ≤ n  →  suc m ≤ suc n
~~~~~~~~~~~

Variables with inferred types can be introduced by `∀`:

~~~~~~~~~~~ {.haskell}
data  _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} →               zero  ≤ n
  s≤s : ∀ {m n} →   m ≤ n  →  suc m ≤ suc n
~~~~~~~~~~~


