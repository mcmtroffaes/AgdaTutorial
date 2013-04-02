% Module System

*[After the Agda Reference Manual](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.Modules)*

\begin{code}
module Modules.Advanced where

open import Data.Nat
\end{code}

Nested modules
==============

Modules are for organizing names of definitions.

Modules can be nested:

\begin{code}
module X where

  x₁ = 10

  module Y where
    y₁ = 11

    module Z where
      z = 12

    y₂ = 13

  x₂ = 14
\end{code}

Indentation is used to indicate which definitions are part of a module.


Qualified names
==============

Names introduced in a module can be accessed by qualification outside of the module:

\begin{code}
module X′ where

  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁

    y₂ = suc Z.z         -- qualified name

  x₂ = suc Y.y₂
  x₂′ = suc (suc Y.Z.z)   -- double qualification
\end{code}


Opening a module
================

One can use short names by opening a module:

\begin{code}
module X″ where

  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁

    y₂ = suc Z.z

    open Z         -- open declaration

    y₂′ = suc z     -- usage

  x₂ = suc Y.y₂
  -- x₂′ = suc (suc Y.z)   -- not allowed!
\end{code}

Note that `open` doesn't remove qualified names.


Public opening (re-exporting)
================

Public opening re-exports the names of the opened modules:

\begin{code}
module X‴ where

  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁

    y₂ = suc Z.z

    open Z public   -- public opening

    y₂′ = suc z

  x₂ = suc Y.y₂
  x₂′ = suc (suc Y.z)   -- usage
\end{code}


Private definitions
===================

Private definitions are inaccessible outside of the module:

\begin{code}
module X⁗ where

  x₁ = 10

  module Y where
    private
      y₁ = suc x₁   -- private definition

    module Z where
      z = suc y₁    -- accessible

    y₂ = suc Z.z

  x₂ = suc Y.y₂
  --  x₂′ = suc (suc (suc Y.y₁))   -- not accessible
\end{code}


Partial opening
===============

One can open part of a module by giving a list of names to open:

\begin{code}
module X⁵ where

  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁
      z′ = z
      z″ = z

    open Z using (z′; z″)  -- partial opening

    y₂ = suc z′     -- usage
    -- y₂′ = suc z     -- not accessible

  x₂ = suc Y.y₂
\end{code}


Partial opening (2)
===============

One can open part of a module by giving a list of names to not open:

\begin{code}
module X⁶ where

  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁
      z′ = z
      z″ = z

    open Z hiding (z)  -- partial opening

    y₂ = suc z′     -- usage
    -- y₂′ = suc z     -- not accessible

  x₂ = suc Y.y₂
\end{code}


Renaming
========

One can open a module and rename some names:

\begin{code}
module X⁷ where

  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁
      z′ = z
      z″ = z

    open Z renaming (z to v; z″ to v″)  -- renamings

    y₂ = suc v     -- usage
    -- y₂″ = suc z     -- not accessible
    y₂′ = suc z′    -- accessible

  x₂ = suc Y.y₂
\end{code}


Mixing modifiers
================

One can mix

-   `using` with `renaming`
-   `hiding` with `renaming`
-   in each case, `public` can be added

Laws
====

-   `open` A `renaming (`ys `to` zs`)`  ≡  
    `open` A `hiding () renaming (`ys `to` zs`)`
-   `open` A `hiding (`xs`) renaming (`ys `to` zs`)`  ≡  
    `open` A `using (`A - xs - ys`) renaming (`ys `to` zs`)`
-   `open` A `renaming ()`  ≡  
    `open` A
