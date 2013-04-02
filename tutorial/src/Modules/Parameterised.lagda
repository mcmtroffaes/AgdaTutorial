% Parameterised Modules

*[After the Agda Reference Manual](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.Modules)*

\begin{code}
module Modules.Parameterised where

open import Data.Nat
\end{code}


Module parameters
==============

Modules may have parameters which are accessible inside the module.

The parameter can filled in outside of the module:

\begin{code}
module X where

  module Y (x₁ : ℕ) where   -- parameter
    y₁ = suc x₁             -- using the parameter
    y₂ = suc y₁

  x₂ = suc (suc (Y.y₁ 10))  -- filling in the parameter
  x₂′ = suc (Y.y₂ 10)
\end{code}


Module application
================

One can define a new module by filling in a module parameter:

\begin{code}
module X′ where

  module Y (x₁ : ℕ) where
    y₁ = suc x₁
    y₂ = suc y₁

  x₂ = suc (Y.y₂ 10)

  module Y′ = Y 10   -- module application

  x₂′ = suc Y′.y₂   -- usage
\end{code}


Opening with module application
================

Opening with module application:

\begin{code}
module X″ where

  module Y (x₁ : ℕ) where
    y₁ = suc x₁
    y₂ = suc y₁

  x₂ = suc (Y.y₂ 10)

  open module Y′ = Y 10   -- opened module application

  x₂′ = suc y₂   -- usage
\end{code}


Mixing modifiers
================


Laws
====

-   `open module` M₁ pars `=` M₂ terms [`public`] mods  ≡  
    `module` M₁ pars `=` M₂ terms mods  
    `open` M₁ [`public`]

