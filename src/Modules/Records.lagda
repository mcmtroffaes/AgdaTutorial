% Record Modules

*[After the Agda Records Tutorial](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.RecordsTutorial)*

\begin{code}
module Modules.Records where

open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}


Record modules
==============

Record defines modules similar to data definitions but these modules
are not automatically opened:

\begin{code}
record R : Set where
  field
    r₁ : Bool
    r₂ : ℕ

x : R
x = record { r₁ = true; r₂ = 2 }
\end{code}

We can open `R`:

\begin{code}
module SimpleOpening where

  open R  -- brings r₁ and r₂ into scope

  y : Bool
  y = r₁ x  -- no qualification
\end{code}


Applied opening
===============

Applied opening also works for `R`:

\begin{code}
module AppliedOpening where

  open R x  -- brings r₁ and r₂ into scope, first parameter filled in 

  y : Bool
  y = r₁
\end{code}

Another example:

\begin{code}
module AppliedOpening′ where

  y : Bool
  y = r₁ where
    open R x
\end{code}

