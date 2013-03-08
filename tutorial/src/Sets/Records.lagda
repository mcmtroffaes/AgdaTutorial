% Records

*[After the Agda Records Tutorial](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.RecordsTutorial)*

\begin{code}
module Sets.Records where

open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq
\end{code}


Record set defintions
==============

A record type is a special set for representing tuples of values.
For example, the following set represents a `Bool`, `ℕ` pair:

\begin{code}
record R : Set where
  field
    r₁ : Bool
    r₂ : ℕ
\end{code}


Record value defintions
==============

An example:

\begin{code}
x : R
x = record { r₁ = true; r₂ = 2 }
\end{code}


Record value defintions with constructors
==============

One could define a constructor for `R` values:

\begin{code}
r : Bool → ℕ → R
r b n = record { r₁ = b; r₂ = n }

x′ = r true 2
\end{code}

Agda provides this definition to us with the following syntax:

\begin{code}
record R′ : Set where
  constructor r′   -- record constructor
  field
    r₁ : Bool
    r₂ : ℕ

x″ = r′ true 2
\end{code}


Field selectors
===============

Agda defines field selectors automatically:

\begin{code}
sel₁ : R → Bool
sel₁ = R.r₁

sel₂ : R → ℕ
sel₂ = R.r₂

x‴ = r (R.r₁ x) (R.r₂ x)
\end{code}


`record` vs. `data` defintions
==============

For every set defined with `record` there is an equivalent set defined with `data`.

For example, the following set is equivalent to `R`:

\begin{code}
data R″ : Set where
  r″ : (r₁ : Bool) (r₂ : ℕ) → R″ 

r₁ : R″ → Bool
r₁ (r″ a b) = a

r₂ : R″ → ℕ
r₂ (r″ a b) = b
\end{code}

Records has the following advantages over `data` definitions:

-   We get seletor functions for free.
-   A record is definitionally equivalent to its recombined parts:  

\begin{code}
extRec : (x : R) → x ≡ r (R.r₁ x) (R.r₂ x)
extRec _ = Eq.refl

-- {- not possible -}
-- extData : (x : R″) → x ≡ r″ (r₁ x) (r₂ x)
-- extData _ = refl
\end{code}


**It is advised to use `record` definitions whenever it is possible.**


Exercises
=========

-   Define `⊤` as a record!
-   Define `_×_` as a record!


Dependent records
=================

The type of a field can depend on the values of the previous fields.

For example the following set is equivalent to `List ℕ`:

\begin{code}
open import Data.Vec using (Vec; []; _∷_)

record Listℕ : Set where
  constructor Lℕ
  field
    length : ℕ
    vector : Vec ℕ length

list : Listℕ
list = Lℕ 3 (0 ∷ 1 ∷ 2 ∷ [])

list′ : Listℕ
list′ = Lℕ _ (0 ∷ 1 ∷ 2 ∷ [])
\end{code}

The type of the selector functions:

\begin{code}
length′ : Listℕ → ℕ 
length′ = Listℕ.length

vector′ : (x : Listℕ) → Vec ℕ (length′ x)   -- dependent
vector′ = Listℕ.vector
\end{code}


Parameterised record
====================

The previous example parameterised with the types of the vector elements:

\begin{code}
record List (A : Set) : Set where
  constructor L
  field
    length : ℕ
    vector : Vec A length

list₂ : List Bool
list₂ = L _ (true ∷ false ∷ true ∷ [])
\end{code}

The type of the selector functions:

\begin{code}
length″ : {A : Set} → List A → ℕ 
length″ = List.length

vector″ : {A : Set} (x : List A) → Vec A (length″ x)   -- dependent
vector″ = List.vector
\end{code}

Note that the parameters became implicit in the field selectors' type.  
(This is a design decision of the Agda language.)


Exercises
=========

Define `Σ` with `record`!


Implicit record fields
======================

TODO


Exercise
========

Define the set of equivalence relations!

\begin{code}
record IsEquivalence {A : Set} (_≈_ : A → A → Set) : Set where
\end{code}

<!--
\begin{code}
  field
    refl  : ∀ {x} → x ≈ x
    sym   : ∀ {x y} → x ≈ y → y ≈ x
    trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
\end{code}
-->

Prove that `_≡_` is an equivalence relation on any set!

\begin{code}
isEquivalence : {A : Set} → IsEquivalence {A} _≡_
\end{code}

<!--
\begin{code}
isEquivalence = record
    { refl = Eq.refl
    ; sym  = Eq.sym
    ; trans = Eq.trans
    }
\end{code}
-->

Exercise
========

Define the set of semigroups!

Prove that `ℕ` is a semigroup with `_+_`!
