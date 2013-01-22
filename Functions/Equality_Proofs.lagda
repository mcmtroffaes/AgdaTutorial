% Proving Equality
% Ambrus Kaposi & Peter Divianszky
% 2012. 11.

\begin{code}
module Functions.Equality_Proofs where
\end{code}

Import List
===========

\begin{code}
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Function using (_$_)         -- 
\end{code}

Propositional equality: `_≡_`
================

Recall the definition of propositional equality:

\begin{code}
data _≡_ {A : Set} (x : A) : A → Set  where
  refl : x ≡ x

infix 4 _≡_
\end{code}

yields

~~~~~~~~~~~~~~~~~ 
refl {ℕ} {0} : 0 ≡ 0
refl {ℕ} {1} : 1 ≡ 1
refl {ℕ} {2} : 2 ≡ 2
...
refl {Bool} {true} : true ≡ true
...
refl {Bool} {not b} : not b ≡ not b   -- if 'b : Bool' is a parameter
...
~~~~~~~~~~~~~~~~~


`_≡_` is an equivalence and a congruence
==============================

`_≡_` is an equivalence-relation:

\begin{code}
refl'  : ∀ {A} (a : A) → a ≡ a
refl' a = refl

sym   : ∀ {A} {a b : A} → a ≡ b → b ≡ a
sym refl = refl   -- after pattern matching on 'refl', 'a' and 'b' coincides
\end{code}

*Exercise*

\begin{code}
trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
\end{code}

<!--
\begin{code}
trans refl refl = refl --
\end{code}
-->

Prove that every function is compatible with the equivalence relation (congruency):

\begin{code}
cong : ∀ {A B} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
\end{code}

<!--
\begin{code}
cong f refl = refl --
\end{code}
-->

Automatic reduction of types
============================

Agda reduces types automatically during type checking.  
This is safe because all functions terminate.

Example:

`1 + 1 ≡ 2`  ⇓  `2 ≡ 2`.

Consequences:

~~~~~~~~~~~~~~~~~ 
refl : 1 + 1 ≡ 2
...
refl : 0 + n ≡ n    -- if 'n : ℕ' is a parameter
...
~~~~~~~~~~~~~~~~~


Definitional and propositional equality
==============================

`x` and `y` are definitionally equal iff `refl : x ≡ y`.

"Definitional equality is trivial equality."

*Example*

\begin{code}
1+1≡2 : 1 + 1 ≡ 2
1+1≡2 = refl
\end{code}

*Counterexample*

Suppose that `n : ℕ` is a parameter.

~~~~~~~~~~~~~~~~~ 
refl : n + 0 ≡ 0 + n   -- type error!
~~~~~~~~~~~~~~~~~

This doesn't typecheck because  
`n + 0 ≡ 0 + n` ⇓ `n + 0 ≡ n`  
and `n + 0` is not the same as `n`.


Proof of `a + 0 ≡ a`
=====================

\begin{code}
+-right-identity : ∀ n → n + 0 ≡ n
+-right-identity zero    = refl
+-right-identity (suc n) = cong suc (+-right-identity n)
\end{code}

So `n + 0 ≡ n` is not trivial,  
but for any `n` we can construct the proof of it.

This is a bit funny though:

~~~~~~~~~~~~~~~~~ 
+-right-identity 0   ⇓  refl
+-right-identity 1   ⇓  refl
+-right-identity 2   ⇓  refl
...
~~~~~~~~~~~~~~~~~

So the code of `+-right-identity` is kind of dead code
(doesn't do any meaningful at run time).  
We'll discuss this later.



Exercises
================================

Finish the ingredients of the proof that (`ℕ`, `_+_`) is a commutative monoid!

\begin{code}
+-left-identity  : ∀ a → 0 + a ≡ a
\end{code}

<!--
\begin{code}
+-left-identity a = refl --
\end{code}
-->

\begin{code}
+-assoc          : ∀ a b c → a + (b + c) ≡ (a + b) + c -- hint: use cong
\end{code}

<!--
\begin{code}
+-assoc zero    b c = refl --
+-assoc (suc a) b c = cong suc (+-assoc a b c) --
\end{code}
| +-identity       : ∀ a → 0 + a ≡ a × a + 0 ≡ a
| +-identity a = +-left-identity a , +-right-identity a --
-->

Fot commutativity you need a helper function first:

\begin{code}
m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
\end{code}

<!--
\begin{code}
m+1+n≡1+m+n zero n = refl  --
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n) --

+-comm : ∀ a b → a + b ≡ b + a
+-comm zero b = sym (+-right-identity b)  --
+-comm (suc n) b = trans  --
  (cong suc (+-comm n b)) --
  (sym (m+1+n≡1+m+n b n)) --
\end{code}
-->


Exercise: `List ⊤` ~ `ℕ`
======================

Let

\begin{code}
fromList : List ⊤ → ℕ
fromList [] = zero
fromList (x ∷ xs) = suc (fromList xs)

toList : ℕ → List ⊤
toList zero = []
toList (suc n) = tt ∷ toList n
\end{code}

Let's prove that `fromList` and `toList` are inverses of each-other and that they preserve the operations `_++_` and `_+_`!

\begin{code}
from-to : ∀ a → fromList (toList a) ≡ a
\end{code}

<!--
\begin{code}
from-to zero = refl  --
from-to (suc a) = cong suc (from-to a)  --
\end{code}
-->

\begin{code}
to-from : ∀ a → toList (fromList a) ≡ a
\end{code}

<!--
\begin{code}
to-from [] = refl  --
to-from (x ∷ n) = cong (_∷_ tt) (to-from n)  --
\end{code}
-->

\begin{code}
fromPreserves++ : ∀ (a b : List ⊤) → fromList (a ++ b) ≡ fromList a + fromList b
\end{code}

<!--
\begin{code}
fromPreserves++ [] b = refl --
fromPreserves++ (x ∷ xs) b = cong suc (fromPreserves++ xs b) --
\end{code}
-->

\begin{code}
toPreserves+ : ∀ (a b : ℕ) → toList (a + b) ≡ toList a ++ toList b
\end{code}

<!--
\begin{code}
toPreserves+ zero    b = refl --
toPreserves+ (suc n) b = cong (_∷_ tt) (toPreserves+ n b) --
\end{code}
-->

Equational reasoning
====================

Equational reasoning is *not* a new language construct!

\begin{code}
_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ refl = refl

infixr 2 _≡⟨_⟩_

_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = refl

infix  2 _∎
\end{code}

Usage example:

\begin{code}
+-comm' : (n m : ℕ) → n + m ≡ m + n
+-comm' zero    n = sym (+-right-identity n)
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
  ≡⟨ cong (λ x → c + x) (distribʳ-*-+ a b c) ⟩
    c + (a * c + b * c)
  ≡⟨ +-assoc c (a * c) (b * c) ⟩
    c + a * c + b * c
  ∎
\end{code}


Define the following functions:

\begin{code}
*-assoc        : ∀ a b c → a * (b * c) ≡ (a * b) * c
\end{code}

<!--
\begin{code}
*-assoc zero b c = refl --
*-assoc (suc a) b c = --
    b * c + a * (b * c) --
  ≡⟨  cong (λ x → (b * c) + x) (*-assoc a b c) ⟩ --
    b * c + a * b * c --
  ≡⟨ sym (distribʳ-*-+ b (a * b) c) ⟩ --
    (b + a * b) * c --
  ∎ --
\end{code}
-->

\begin{code}
*-left-identity  : ∀ a → 1 * a ≡ a
\end{code}

<!--
\begin{code}
*-left-identity a = +-right-identity a --
\end{code}
-->

\begin{code}
*-right-identity : ∀ a → a * 1 ≡ a
\end{code}

<!--
\begin{code}
*-right-identity zero    = refl --
*-right-identity (suc n) = cong suc (*-right-identity n) --
*-identity       : ∀ a → 1 * a ≡ a × a * 1 ≡ a --
*-identity a = *-left-identity a , *-right-identity a --
\end{code}
-->

Commutativity:

\begin{code}
-- helper functions:
n*0≡0 : ∀ n → n * 0 ≡ 0
\end{code}

<!--
\begin{code}
n*0≡0 zero    = refl --
n*0≡0 (suc n) = n*0≡0 n --
\end{code}
-->

\begin{code}
*-suc : ∀ n m → n + n * m ≡ n * suc m
\end{code}

<!--
\begin{code}
*-suc zero m = refl --
*-suc (suc n) m = cong suc $ --
    n + (m + n * m) --
  ≡⟨ +-assoc n m (n * m) ⟩ --
    n + m + n * m --
  ≡⟨ cong (λ x → x + n * m) $ +-comm n m  ⟩ --
    m + n + n * m --
  ≡⟨ sym $ +-assoc m n (n * m) ⟩ --
    m + (n + n * m) --
  ≡⟨ cong (λ x → m + x) $ *-suc n m ⟩ --
    m + n * suc m --
  ∎ --
  -- hint: you will need steps like this: cong (λ x → n + x) ...
\end{code}
-->

\begin{code}
*-comm : ∀ m n → m * n ≡ n * m
\end{code}

<!--
\begin{code}
*-comm zero n = sym $ n*0≡0 n --
*-comm (suc m) n =  --
    n + m * n --
  ≡⟨ cong (λ x → n + x) (*-comm m n) ⟩ --
    n + n * m --
  ≡⟨ *-suc n m ⟩ --
    n * suc m --
  ∎ --
\end{code}
-->

<!--
| Browse and read the Agda standard libraries: [http://www.cse.chalmers.se/\~nad/listings/lib-0.5/](http://www.cse.chalmers.se/~nad/listings/lib-0.5/)
-->

Semiring solver
===============

\begin{code}
module trySemiringSolver where

open import Data.Nat
open import Data.Nat.Properties
open SemiringSolver
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _≡-official_)

f : ∀ a b c → a + b * c + 1 ≡-official 1 + c * b + a
f = solve 3 (λ a b c → a :+ b :* c :+ con 1 := con 1 :+ c :* b :+ a) refl
\end{code}



