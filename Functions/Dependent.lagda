% Dependently Typed Functions


\begin{code}
module Functions.Dependent where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_)
open import Data.Fin using (Fin; zero; suc)
\end{code}


Dependently typed functions
===============

Dependently typed function:

`f : (x : A) → B`, where `B` may depend on `x`

*Example*  

\begin{code}
fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero = zero  -- Note: different zeros
fromℕ (suc n) = suc (fromℕ n)
\end{code}

*Notes*

-   The dependent function spaces are called `Π`-types because
    the number of elements can be given as a product:  
    ∣`(x : A)→ B`∣ = ∏`x`∈`A` ∣`B`∣, for example  
    ∣`(n : Fin m)→ Fin (suc n)`∣ = (`m` + 1)!
-   Polymorph functions like `(A : Set) → A → A` are special cases of dependent functions.
-   Non-dependent functions like `A → B` are special special cases of dependent functions  
    (`(x : A) → B` where `B` doesn't depend on `x`).




Exercises
=========

Define a substraction with restricted domain:

\begin{code}
_-_ : (n : ℕ) → Fin (suc n) → ℕ
\end{code}

<!--
\begin{code}
zero - zero = zero
zero - suc ()
suc n - zero = suc n
suc n - suc m = n - m
\end{code}
-->

Define `toℕ`:

\begin{code}
toℕ : ∀ {n} → Fin n → ℕ
\end{code}

<!--
\begin{code}
toℕ zero    = zero
toℕ (suc n) = suc (toℕ n)
\end{code}
-->

Define `fromℕ≤` such that `toℕ (fromℕ≤ e)` is `m` if `e : m < n`:

\begin{code}
fromℕ≤ : ∀ {m n} → m < n → Fin n
\end{code}

<!--
\begin{code}
fromℕ≤ (s≤s z≤n)       = zero
fromℕ≤ (s≤s (s≤s m≤n)) = suc (fromℕ≤ (s≤s m≤n))
\end{code}
-->

Define `inject+` such that `toℕ (inject+ n i)` is the same as `toℕ i`:

\begin{code}
inject+ : ∀ {m} n → Fin m → Fin (m + n)
\end{code}

<!--
\begin{code}
inject+ n zero    = zero
inject+ n (suc i) = suc (inject+ n i)
\end{code}
-->

Define `four` such that `toℕ four` is `4`:

\begin{code}
four : Fin 66
\end{code}

<!--
\begin{code}
four = inject+ 61 (fromℕ 4)
\end{code}
-->

Define `raise` such that `toℕ (raise n i)` is the same as `n + toℕ i`:

\begin{code}
raise : ∀ {m} n → Fin m → Fin (n + m)
\end{code}

<!--
\begin{code}
raise zero i = i
raise (suc n) i = suc (raise n i)
\end{code}
-->

Define `fin≤`:

\begin{code}
fin≤ : ∀ {n}(m : Fin n) → toℕ m < n
\end{code}

<!--
\begin{code}
fin≤ zero    = s≤s z≤n
fin≤ (suc m) = s≤s (fin≤ m)
\end{code}
-->