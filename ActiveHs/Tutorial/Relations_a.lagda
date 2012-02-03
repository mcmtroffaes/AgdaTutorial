% Predicates
% Péter Diviánszky
% 2011. 05. 03.

\begin{code}
module Relations_a where
\end{code}



`_≤_`: Less-Or-Equal Predicate
==========

Predicates are indexed/parametrized sets with at most 1 element.

*Example:*  
`m ≤ n` has exactly one element if `m` less or equal than `n`:

\begin{code}
data  _≤_ : ℕ → ℕ → Set  where
  z≤n : (n : ℕ)           → zero  ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n
\end{code}

Set           1st,      2nd,            3rd,                   ...
------------- --------- --------------- ---------------------- ---
`0 ≤ 0` = {   `z≤n 0` }
`0 ≤ 1` = {   `z≤n 1` }
`0 ≤ 2` = {   `z≤n 2` }
...           ...       
`1 ≤ 0` = { } 
`1 ≤ 1` = {             `s≤s (z≤n 0)` }
`1 ≤ 2` = {             `s≤s (z≤n 1)` }
...                     ...             
`2 ≤ 0` = { } 
`2 ≤ 1` = { }
`2 ≤ 2` = {                             `s≤s (s≤s (z≤n 1))` }
...                                     ...                    
...           ...       ...             ...                    ...


******************************

*Exercise:*  
Explore the elements of the alternative definition:

\begin{code}
data _≤′_ (m : ℕ) : ℕ → Set where
  ≤′-refl :                    m ≤′ m
  ≤′-step : {n : ℕ} → m ≤′ n → m ≤′ suc n
\end{code}

*Exercise:*  
Explore the elements of the sublist predicate:

\begin{code}
data _⊆_ {A : Set} : List A → List A → Set where
    stop :                                              [] ⊆ []
    drop : {xs ys : List A} → {y : A} → xs ⊆ ys →       xs ⊆ (y ∷ ys)
    keep : {xs ys : List A} → {x : A} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)
\end{code}

|[] ⊆ [] = {stop}  
|1 ∷ [] ⊆ [] = {}  
|[] ⊆ 1 ∷ [] = {drop [] 1 [] stop}  
|1 ∷ [] ⊆ 1 ∷ [] = {keep 1 [] [] stop}  



`_≡_`: Propositional Equality
======================

Maybe scaring for beginners, but this is just a simple predicate:

\begin{code}
data  _≡_ {A : Set} : A → A → Set  where
  refl : (x : A) → x ≡ x
\end{code}

*Examples:*

Set           1st,      2nd, 3rd, ...
------------- --------- ---------------
`0 ≡ 0` = {   `refl 0` }
`0 ≡ 1` = { }
`0 ≡ 2` = { }
...                  
`1 ≡ 0` = { } 
`1 ≡ 1` = {   `refl 1` }
`1 ≡ 2` = { }
...                        
`2 ≡ 0` = { } 
`2 ≡ 1` = { }
`2 ≡ 2` = {   `refl 2` }
...           
...           ...     


***********************

*Exercise:*  
Explore the elements of the alternative definition for natural numbers:

\begin{code}
data _≡₂_ : ℕ → ℕ → Set where
  zz :                       zero ≡₂ zero
  ss : {a b : ℕ} → a ≡₂ b → suc a ≡₂ suc b
\end{code}

*Exercise:*  
Explore the elements of the following set:

\begin{code}
data _≠_ : ℕ → ℕ → Set where
  z≠s : {n : ℕ} →            zero ≠ suc n
  s≠z : {n : ℕ} →           suc n ≠ zero
  s≠s : {m n : ℕ} → m ≠ n → suc m ≠ suc n
\end{code}


******************

*Exercise:*  
Explore the elements of `All (λ n → n ≤ 3)` given the definition

\begin{code}
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : {x : A} → {xs : List A} → P x → All P xs → All P (x ∷ xs)
\end{code}



    - összeadás, kivonás, ...


    -   ind. család refaktoring

