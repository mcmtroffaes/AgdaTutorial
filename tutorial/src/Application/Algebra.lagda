% Abstract Algebra in Agda

\begin{code}
module Application.Algebra where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid)

import Relation.Binary.EqReasoning as EqR
\end{code}


Semigroup property
=====================

Let `A` be a type and let `_∙_` be a binary operation on `A`.
`A` with `_∙_` forms a semigroup iff `_∙_` is associative.

We can model the semigroup proposition as follows:

\begin{code}
record IsSemigroup {A : Set} (_∙_ : A → A → A) : Set where
  field
    assoc         : ∀ x y z →  (x ∙ y) ∙ z  ≡  x ∙ (y ∙ z)
\end{code}


Exercise
========

Prove that `ℕ` with `_+_` forms a semigroup!

\begin{code}
ℕ+-isSemigroup : IsSemigroup _+_
\end{code}

<!--
\begin{code}
ℕ+-isSemigroup = record
  { assoc = +-assoc
  }
 where
  +-assoc : ∀ x y z →  (x + y) + z  ≡  x + (y + z)
  +-assoc zero    _ _ = refl
  +-assoc (suc m) n o = cong suc (+-assoc m n o)
\end{code}
-->


Usage
=====

Usage example:

\begin{code}
module Usage₁ where
  open IsSemigroup

  ex : ∀ n → (n + 1) + 1 ≡ n + 2
  ex n = assoc ℕ+-isSemigroup n 1 1
\end{code}

With applied module opening:

\begin{code}
module Usage₂ where
  open IsSemigroup ℕ+-isSemigroup

  ex : ∀ n → (n + 1) + 1 ≡ n + 2
  ex n = assoc n 1 1
\end{code}

With local module opening:

\begin{code}
module Usage₃ where
  ex : ∀ n → (n + 1) + 1 ≡ n + 2
  ex n = assoc n 1 1  where
    open IsSemigroup ℕ+-isSemigroup
\end{code}


Monoid property
==================

`IsMonoid {A} _∙_ ε` represents the proposition that
(`A`, `_∙_`, `ε`) is a monoid:

\begin{code}
record IsMonoid {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
  field
    isSemigroup : IsSemigroup _∙_
    identity    : (∀ x → ε ∙ x ≡ x)  ×  (∀ x → x ∙ ε ≡ x)

  open IsSemigroup isSemigroup public
\end{code}

Public opening at the end makes usage of `IsMonoid` easier.


Exercise
========

Prove that (`ℕ`, `_+_`, `0`) forms a monoid!

\begin{code}
ℕ+0-isMonoid : IsMonoid _+_ 0
\end{code}

<!--
\begin{code}
ℕ+0-isMonoid = record
  { isSemigroup = ℕ+-isSemigroup
  ; identity = left-identity , right-identity
  }
 where
  left-identity : ∀ n → 0 + n ≡ n
  left-identity _ = refl

  right-identity : ∀ n → n + 0 ≡ n
  right-identity zero = refl
  right-identity (suc n) = cong suc (right-identity n)
\end{code}
-->


Usage
=====

Usage example:

\begin{code}
module Usage₄ where
  ex : ∀ n → (n + 0) + n ≡ n + n
  ex n = cong (λ x → x + n) (proj₂ identity n)  where
    open IsMonoid ℕ+0-isMonoid

  ex′ : ∀ n → (n + 0) + n ≡ n + n
  ex′ n = assoc n 0 n  where
    open IsMonoid ℕ+0-isMonoid   -- we opened IsMonoid, not IsSemigroup
\end{code}


Named binary operations
=======================

Instead of `A → A → A` we can write `Op₂ A` if we define

\begin{code}
Op₂ : Set → Set
Op₂ A = A → A → A
\end{code}

Thus we can write

\begin{code}
record IsSemigroup′ {A : Set} (_∙_ : Op₂ A) : Set where
  field
    assoc         : ∀ x y z →  (x ∙ y) ∙ z  ≡  x ∙ (y ∙ z)
\end{code}


Exercise
========

Define the type of unary operations as `Op₁`!

<!--
\begin{code}
Op₁ : Set → Set
Op₁ A = A → A
\end{code}
-->


Named function properties
=========================

We can name functions properties like

\begin{code}
Associative : {A : Set} → Op₂ A → Set
Associative _∙_ = ∀ x y z →  (x ∙ y) ∙ z  ≡  x ∙ (y ∙ z)
\end{code}

After this definition we can write

\begin{code}
record IsSemigroup″ {A : Set} (_∙_ : Op₂ A) : Set where
  field
    assoc         : Associative _∙_
\end{code}


Exercises
=========

Define the following function properties!

\begin{code}
Commutative : {A : Set} → Op₂ A → Set _
\end{code}

<!--
\begin{code}
Commutative _∙_ = ∀ x y →  x ∙ y  ≡  y ∙ x
\end{code}
-->

The first parameter of `LeftIdentity` is the neutral element.

\begin{code}
LeftIdentity : {A : Set} → A → Op₂ A → Set _
\end{code}

<!--
\begin{code}
LeftIdentity e _∙_ = ∀ x →  e ∙ x  ≡  x
\end{code}
-->

\begin{code}
RightIdentity : {A : Set} → A → Op₂ A → Set _
\end{code}

<!--
\begin{code}
RightIdentity e _∙_ = ∀ x →  x ∙ e  ≡  x
\end{code}
-->

\begin{code}
Identity : {A : Set} → A → Op₂ A → Set _
\end{code}

<!--
\begin{code}
Identity e ∙ = LeftIdentity e ∙ × RightIdentity e ∙
\end{code}
-->


Commutative monoid property
==============================

Consider the following definition of the commutative monoid proposition:

\begin{code}
record IsCommutativeMonoid′ {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
  field
    isMonoid : IsMonoid _∙_ ε
    comm     : Commutative _∙_
\end{code}

This definition is correct, but redundant because
commutativity and left identity properties entail the right identity
property.

A non-redundant and still easy-to-use definition is the following:

\begin{code}
record IsCommutativeMonoid {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
  field
    isSemigroup : IsSemigroup _∙_
    identityˡ   : LeftIdentity ε _∙_
    comm        : Commutative _∙_

  open IsSemigroup isSemigroup public

  identity : Identity ε _∙_
  identity = (identityˡ , identityʳ)
    where
    open EqR (setoid A)

    identityʳ : RightIdentity ε _∙_
    identityʳ = λ x → begin
      (x ∙ ε)  ≈⟨ comm x ε ⟩
      (ε ∙ x)  ≈⟨ identityˡ x ⟩
      x        ∎

  isMonoid : IsMonoid _∙_ ε
  isMonoid = record
    { isSemigroup = isSemigroup
    ; identity    = identity
    }
\end{code}

-   When constructing `IsCommutativeMonoid`, we should
    provide the semigroup, left identity and commutativity properties.
-   When using `IsCommutativeMonoid`, we have
    semigroup, associativity, monoid, identity and commutativity properties.


Exercises
=========

A) Define the group property!

B) Define the abelian group property!


The type of all semigroups
==========================

We can define the type of semigroups as

\begin{code}
record Semigroup : Set₁ where
  infixl 7 _∙_
  field
    Carrier     : Set
    _∙_         : Op₂ Carrier
    isSemigroup : IsSemigroup _∙_

  open IsSemigroup isSemigroup public
\end{code}


Exercises
=========

A) Prove that (ℕ, +) is a semigroup (by proving that there is
a corresponding element of `Semigroup`)!

B) Define the types of all monoids as a record with fields `Carrier`, `_∙_`, `ε` and `isMonoid`!

<!--
\begin{code}
record Monoid : Set₁ where
  infixl 7 _∙_
  field
    Carrier  : Set
    _∙_      : Op₂ Carrier
    ε        : Carrier
    isMonoid : IsMonoid _∙_ ε

  open IsMonoid isMonoid public

  semigroup : Semigroup
  semigroup = record { isSemigroup = isSemigroup }
\end{code}
-->


Some defined operations
=======================

We can define the multiplication by a natural number in any monoid:

\begin{code}
module MonoidOperations (m : Monoid) where

  open Monoid m

  infixr 7 _×′_

  _×′_ : ℕ → Carrier → Carrier
  0     ×′ x = ε
  suc n ×′ x = x ∙ (n ×′ x)
\end{code}



Standard Library definitions
================

You can find the given definitions in the following Standard Library modules:

\begin{code}
import Algebra.FunctionProperties using (Op₁; Op₂)
import Algebra.FunctionProperties using (Associative; Commutative; LeftIdentity; RightIdentity; Identity) -- and more function properties
import Algebra.Structures using (IsSemigroup; IsMonoid; IsCommutativeMonoid) -- and more
import Algebra using (Semigroup; Monoid; CommutativeMonoid) -- and more
import Algebra.Operations -- some defined operations

import Data.Nat.Properties using (isCommutativeSemiring) -- this contains definitions like ℕ+0-isMonoid
\end{code}

Notable differences

-   The definitions are generalized from `_≡_` to an arbitrary equivalence relation.
-   The definitions are universe polymorphic (see later).

Example usage

\begin{code}
module StdLibUsage where
  open import Algebra.Structures as A using (IsCommutativeMonoid)
  open import Data.Nat.Properties using (isCommutativeSemiring)

  open A.IsCommutativeSemiring
  open A.IsCommutativeMonoid (+-isCommutativeMonoid isCommutativeSemiring)

  ex : ∀ n → (n + 1) + 1 ≡ n + 2
  ex n = assoc n 1 1
\end{code}
