% Views
% Péter Diviánszky
% 2011. 05. 03.

\begin{code}
module Views_a where
\end{code}


Tehát a halmazoknak nem csak az elemszáma számít, hanem az elemek szerkezete is.

N részleges elemei:
n      -- semmit nem tudunk
suc y   -- nem nulla természetes szám, aminek a megelőzője y
suc (suc z)  -- 1-től nagyobb természetes szám, amiből ha kettőt kivonunk z-t kapunk


Order 3 4  részleges elemei:
x = less n m = less 3 0   -- itt nincsnek külön elemek!

Order a b
less n m     -- n = a, n + (suc m) = b

Order 3 b
less n m     -- n = 3, n + (suc m) = b

⊥ részleges elemei:
nincs (illetve ha találunk abból ellentmondást vezethetünk le)

Fin n részleges elemei:
k   --   n /= 0 !     ( {n : N} (k : Fin n) -> 1 <= n




`Ordering`: Ordering View
=========================

Views are families of sets which has always 1 element.

*Example:*  
A set which helps to decide the relation between two naturals:

\begin{code}
_+_ : ℕ → ℕ → ℕ
zero  + x = x
suc y + x = suc (y + x)

infixl 6 _+_

data Ordering : ℕ → ℕ → Set where
  less    : (m k : ℕ) → Ordering m (1 + m + k)
  equal   : (m   : ℕ) → Ordering m m
  greater : (m k : ℕ) → Ordering (1 + m + k) m
\end{code}

Elements:

Set                1st,            2nd, 3rd, ...
------------------ --------------- --------------
`Ordering 0 0` = { `equal 0` }  
`Ordering 0 1` = { `less 0 0` }  
`Ordering 0 2` = { `less 0 1` }  
`Ordering 0 3` = { `less 0 2` }  
...  
`Ordering 1 0` = { `greater 0 0` }  
`Ordering 1 1` = { `equal 1` }  
`Ordering 1 2` = { `less 1 0` }  
`Ordering 1 3` = { `less 1 1` }  
...

Notes

-   The definition of `_+_` is discussed later.
-   The first parameter of the constructors is the minimum.
-   The optional second parameter is the difference minus one.
-   `Ordering n m`  ~   `(suc n ≤ m)  ⊎  (n ≡ m)  ⊎  (suc m ≤ n)`.


**********************


*Exercise:*  
Explore the elements of the following set:

\begin{code}
_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n

infixl 7 _*_

data Parity : ℕ → Set where
    even : (k : ℕ) → Parity (k * 2)
    odd  : (k : ℕ) → Parity (1 + k * 2)
\end{code}

|Parity zero = { even zero }  
|Parity (suc zero) = { odd zero }  
|Parity (suc (suc zero)) = { even (suc zero) }  
|Parity (suc (suc (suc zero))) = { odd (suc zero) }  



