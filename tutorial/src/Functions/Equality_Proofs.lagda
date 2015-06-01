% Proving Equality
% Ambrus Kaposi & Peter Divianszky
% 2012. 11.

\begin{code}
module Functions.Equality_Proofs where
\end{code}

Import list
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
=============================

Recall the definition of propositional equality:

\begin{code}
data _≡_ {A : Set} (x : A) : A → Set  where
  refl : x ≡ x

infix 4 _≡_
\end{code}

that yields the following statements:

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

`_≡_` as an equivalence and a congruence
========================================

Note that `_≡_` is an equivalence relation:

\begin{code}
refl'  : ∀ {A} (a : A) → a ≡ a
refl' a = refl

sym   : ∀ {A} {a b : A} → a ≡ b → b ≡ a
sym refl = refl
\end{code}

In the definition of `sym`, we can prove the symmetry with pattern matching on
`refl`, in which case `a` and `b` coincides.

Exercises
---------

1. Prove that `≡` is a transitive relation:

     `trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c`

1. Prove that every function is compatible with the equivalence relation,
   which is called congruency:

     `cong : ∀ {A B} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n`

<!--
\begin{code}
trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl --

cong : ∀ {A B} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
cong f refl = refl --
\end{code}
-->

Automatic reduction of types
============================

Agda reduces types automatically during type checking.  That is safe because
all functions terminate (that is, they are all total functions).  For example:

`1 + 1 ≡ 2`  ⇓  `2 ≡ 2`.

Note the consequences:

~~~~~~~~~~~~~~~~~
refl : 1 + 1 ≡ 2
...
refl : 0 + n ≡ n    -- if 'n : ℕ' is a parameter
...
~~~~~~~~~~~~~~~~~

Definitional and propositional equality
=======================================

`x` and `y` are definitionally equal iff `refl : x ≡ y`.

"Definitional equality is trivial equality."

As an example, consider the following:

\begin{code}
1+1≡2 : 1 + 1 ≡ 2
1+1≡2 = refl
\end{code}

While as a counterexample, consider this.  Suppose that `n : ℕ` is a
parameter.

~~~~~~~~~~~~~~~~~
refl : n + 0 ≡ 0 + n
~~~~~~~~~~~~~~~~~

Here, we will get a type error, that is it will not typecheck
because `n + 0 ≡ 0 + n` ⇓ `n + 0 ≡ n`  and `n + 0` is not the
same as `n`.

Proof of `a + 0 ≡ a`
====================

\begin{code}
+-right-identity : ∀ n → n + 0 ≡ n
+-right-identity zero    = refl
+-right-identity (suc n) = cong suc (+-right-identity n)
\end{code}

Thus `n + 0 ≡ n` is not trivial to prove, but for any `n`, we can construct the
proof for it.  While that is a bit funny though:

~~~~~~~~~~~~~~~~~
+-right-identity 0   ⇓  refl
+-right-identity 1   ⇓  refl
+-right-identity 2   ⇓  refl
...
~~~~~~~~~~~~~~~~~

That is, the code of `+-right-identity` is kind of dead code (which does not do
anything meaningful at run time).  We will come back to this later.

Exercises
---------

Finish the ingredients of the proof that (`ℕ`, `_+_`) is a commutative monoid!

\begin{code}
+-left-identity  : ∀ a → 0 + a ≡ a
+-assoc          : ∀ a b c → a + (b + c) ≡ (a + b) + c -- hint: use cong
\end{code}

<!--
\begin{code}
+-left-identity a = refl --

+-assoc zero    b c = refl --
+-assoc (suc a) b c = cong suc (+-assoc a b c) --
\end{code}
| +-identity       : ∀ a → 0 + a ≡ a × a + 0 ≡ a
| +-identity a = +-left-identity a , +-right-identity a --
-->

For proving the commutativity, you will need a helper function first:

\begin{code}
m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
+-comm      : ∀ a b → a + b ≡ b + a
\end{code}

<!--
\begin{code}
m+1+n≡1+m+n zero n = refl  --
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n) --

+-comm zero b = sym (+-right-identity b)  --
+-comm (suc n) b = trans  --
  (cong suc (+-comm n b)) --
  (sym (m+1+n≡1+m+n b n)) --
\end{code}
-->

Exercise: `List ⊤` ~ `ℕ`
------------------------

Consider the following function definitions:

\begin{code}
fromList : List ⊤ → ℕ
fromList []       = zero
fromList (x ∷ xs) = suc (fromList xs)

toList : ℕ → List ⊤
toList zero    = []
toList (suc n) = tt ∷ toList n
\end{code}

Let us prove that `fromList` and `toList` are inverses of each other and that
they preserve the `_++_` and `_+_` operations.

\begin{code}
from-to : ∀ a → fromList (toList a) ≡ a
to-from : ∀ a → toList (fromList a) ≡ a

fromPreserves++ : ∀ (a b : List ⊤) → fromList (a ++ b) ≡ fromList a + fromList b
toPreserves+    : ∀ (a b : ℕ) → toList (a + b) ≡ toList a ++ toList b
\end{code}

<!--
\begin{code}
from-to zero    = refl  --
from-to (suc a) = cong suc (from-to a)  --

to-from []      = refl  --
to-from (x ∷ n) = cong (_∷_ tt) (to-from n)  --

fromPreserves++ [] b = refl --
fromPreserves++ (x ∷ xs) b = cong suc (fromPreserves++ xs b) --

toPreserves+ zero    b = refl --
toPreserves+ (suc n) b = cong (_∷_ tt) (toPreserves+ n b) --
\end{code}
-->

Equational reasoning
====================

Equational reasoning is *not* a new language construct.

\begin{code}
_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ refl = refl

infixr 2 _≡⟨_⟩_

_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = refl

infix  3 _∎
\end{code}

This could be then used in the following way:

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
===================

We would like to prove that (`ℕ`, `_*_`) is a commutative monoid.  In order
to do so, first we will need distributivity:

\begin{code}
distribʳ-*-+ : ∀ a b c → (a + b) * c ≡ a * c + b * c
distribʳ-*-+ zero    b c = refl
distribʳ-*-+ (suc a) b c =
    c + (a + b) * c
  ≡⟨ cong (λ x → c + x) (distribʳ-*-+ a b c) ⟩
    c + (a * c + b * c)
  ≡⟨ +-assoc c (a * c) (b * c) ⟩
    c + a * c + b * c
  ∎
\end{code}

We can also see that the proof involves using the so-called λ-functions.  Such
functions are basically functions without names, and can be used at places
where we would have defined a function for a single use only.

Their syntax is as follows:

~~~~
λ x → E(x)
~~~~

where `x` is a variable bound by `λ` as a quantifier, and `E(x)` is the scope
of this variable.  It corresponds to such a function, with the name, `f`
missing:

~~~~
f x = E(x)
~~~~

Define the following functions (or, rather, prove the following series of
lemmata):

\begin{code}
*-assoc          : ∀ a b c → a * (b * c) ≡ (a * b) * c
*-left-identity  : ∀ a → 1 * a ≡ a
*-right-identity : ∀ a → a * 1 ≡ a
*-identity       : ∀ a → 1 * a ≡ a × a * 1 ≡ a
\end{code}

<!--
\begin{code}
*-assoc zero    b c = refl --
*-assoc (suc a) b c = --
    b * c + a * (b * c) --
  ≡⟨  cong (λ x → (b * c) + x) (*-assoc a b c) ⟩ --
    b * c + a * b * c --
  ≡⟨ sym (distribʳ-*-+ b (a * b) c) ⟩ --
    (b + a * b) * c --
  ∎ --

*-left-identity a = +-right-identity a --

*-right-identity zero    = refl --
*-right-identity (suc n) = cong suc (*-right-identity n) --

*-identity a = *-left-identity a , *-right-identity a --
\end{code}
-->

Proving commutativity:

\begin{code}
n*0≡0  : ∀ n → n * 0 ≡ 0
*-suc  : ∀ n m → n + n * m ≡ n * suc m
*-comm : ∀ m n → m * n ≡ n * m
\end{code}

<!--
\begin{code}
n*0≡0 zero    = refl --
n*0≡0 (suc n) = n*0≡0 n --

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

*-comm zero n = sym $ n*0≡0 n --
*-comm (suc m) n =  --
    n + m * n --
  ≡⟨ cong (λ x → n + x) (*-comm m n) ⟩ --
    n + n * m --
  ≡⟨ *-suc n m ⟩ --
    n * suc m --
  ∎ --
\end{code}
| Browse and read the Agda standard libraries: [http://www.cse.chalmers.se/\~nad/listings/lib-0.5/](http://www.cse.chalmers.se/~nad/listings/lib-0.5/)
-->

Semiring solver
===============

As another approach to proving certain properties about operations, one may
consider using the `SemiringSolver` module.  This exports the `solve` function
that could be fed with the abstract representation of the theorem to be
proven, and then it tries to find (construct) a proof for that.

Note that it has to be imported together with the `Data.Nat.Properties`
module.

\begin{code}
module trySemiringSolver where

open import Data.Nat
open import Data.Nat.Properties
open SemiringSolver
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _≡-official_)

f : ∀ a b c → a + b * c + 1 ≡-official 1 + c * b + a
f = solve 3 (λ a b c → a :+ b :* c :+ con 1 := con 1 :+ c :* b :+ a) refl
\end{code}
