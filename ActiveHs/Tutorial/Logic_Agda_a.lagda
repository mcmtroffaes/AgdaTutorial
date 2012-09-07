% Logic (Agda)
% Ambrus Kaposi
% 2011. 11. 24.

\begin{code}
module Logic_Agda_a where
\end{code}


First order logic
================

Agda's type system incorporates constructive first order logic (predicate logic).

In the Hilbert-style calculus, first order logic has 4 additional axioms to the ones previously defined. The inference rule is the same.

    Additional axioms
    ---------------------------------------------------
    ∀-gen   (P ⇒ Q) ⇒ (P ⇒ ∀x:Q), if x is not free in P
    ∃-gen   (P ⇒ Q) ⇒ (∃x:P ⇒ Q), if x is not free in Q
    ∀-pred  ∀x:P ⇒ P[t/x], if t is free for x in P
    ∃-pred  P[t/x] ⇒ ∃x:P, if t is free for x in P

Curry-Howard correspondance:

    Logic       Haskell            Agda
    --------------------------------------------
    ⇒           ->                 →
    True        ()                 ⊤
    False       Not ()             ⊥
    And         (,)                _×_
    Or          Either             _⊎_
    Not P       forall s. p -> s   λ P → ⊥
    Iff         (p->q, q->p)       P → Q × Q → P
    ∀x∈A:P(x)                      (x : A) → P x  (this is also called Π (Pi) type)
    ∃x∈A:P(x)                      Σ A P

The logic incorporated in Agda's type system is safe because of termination check and totality.


Agda exercises
==============

Imports:

\begin{code}
open import Data.Empty   using (⊥)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])
open import Function using (const)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)
open SemiringSolver

_⇔_ : Set → Set → Set
x ⇔ y = (x → y) × (y → x)
infix 1 _⇔_
\end{code}

*Exercise:* prove that the following hold in Agda. The type is given for some of them as a help.

\begin{code}
-- Axioms:
------------------------------------------------
-- implUnit     P ⇒ (Q ⇒ P)
implUnit : {P Q : Set} → P → (Q → P)
implUnit = const --
-- implDistr    (P ⇒ (Q ⇒ R)) ⇒ ((P ⇒ Q) ⇒ (P ⇒ R))
implDistr : {P Q R : Set} → (P → (Q → R)) → ((P → Q) → (P → R)) --
implDistr pqr pq p = pqr p (pq p) --
-- conjElim1    P ∧ Q ⇒ P
conjElim1 : {P Q : Set} → P × Q → P
conjElim1 = proj₁ --
-- conjElim2    P ∧ Q ⇒ Q
conjElim2 : {P Q : Set} → P × Q → Q --
conjElim2 = proj₂ --
-- conjIntr     P ⇒ (Q ⇒ (P ∧ Q))
conjIntr : {P Q : Set} → P → Q → P × Q --
conjIntr = _,_ --
-- disjIntr1    P ⇒ (P ∨ Q)
disjIntr1 : {P Q : Set} → P → P ⊎ Q
disjIntr1 = inj₁ --
-- disjIntr2    Q ⇒ (P ∨ Q)
disjIntr2 : {P Q : Set} → Q → P ⊎ Q --
disjIntr2 = inj₂ --
-- disjElim     (P ⇒ R) ⇒ ((Q ⇒ R) ⇒ ((P ∨ Q) ⇒ R))
disjElim : {P Q R : Set} → (P → R) → ((Q → R) → ((P ⊎ Q) → R)) --
disjElim = [_,_] --
-- reductioAbs  (P ⇒ Q) ⇒ ((P ⇒ ¬Q) ⇒ ¬P)
reductioAbs : {P Q : Set} → (P → Q) → ((P → ¬ Q) → ¬ P)
reductioAbs pq pnq p = pnq p (pq p) --
-- contradict   P ⇒ (¬P ⇒ Q)
contradict : {P Q : Set} → P → ¬ P → Q --
contradict p np with np p  --
contradict p np | () --
-- exclMiddle   P ∨ ¬P -- this cannot be proven in Agda
-- exclMiddle : {P : Set} → P ⊎ ¬ P --
-- exclMiddle = ? --
-- equivElim1   (P ⇔ Q) ⇒ (P ⇒ Q)
equivElim1 : {P Q : Set} → (P ⇔ Q) → (P → Q)
equivElim1 = proj₁ --
-- equivElim2   (P ⇔ Q) ⇒ (Q ⇒ P)
equivElim2 : {P Q : Set} → (P ⇔ Q) → (Q → P) --
equivElim2 = proj₂ --
-- equivIntr    (P ⇒ Q) ⇒ ((Q ⇒ P) ⇒ (P ⇔ Q))
equivIntr : {P Q : Set} → (P → Q) → ((Q → P) → (P ⇔ Q)) --
equivIntr = _,_ --

-- Additional axioms
-- ---------------------------------------------------
-- ∀-gen   (P ⇒ Q) ⇒ (P ⇒ ∀x:Q), if x is not free in P
-- ∃-gen   (P ⇒ Q) ⇒ (∃x:P ⇒ Q), if x is not free in Q
-- ∀-pred  ∀x:P ⇒ P[t/x], if t is free for x in P
-- ∃-pred  P[t/x] ⇒ ∃x:P, if t is free for x in P
-- TODO --
-- 
-- Inference rule:
-- ------------------------------------------------
-- modusPonens  ((P ⇒ Q) ∧ P) ⇒ Q
modusPonens : {P Q : Set} → ((P → Q) × P) → Q --
modusPonens (pq , p) = pq p --

-- assoc       P ∧ (Q ∧ R) ⇒ (P ∧ Q) ∧ R
assoc : {P Q R : Set} → (P × (Q × R)) → ((P × Q) × R) --
assoc (p , q , r) = (p , q) , r --
-- andIdemp    P ∧ P ⇔ P
andIdemp : {P : Set} → (P × P) ⇔ P --
andIdemp = proj₁ , (λ p → p , p) --
-- andOrDistr  P ∧ (Q ∨ R) ⇔ (P ∧ Q) ∨ (P ∧ R)
andOrDistr : {P Q R : Set} → (P × (Q ⊎ R)) ⇔ (P × Q ⊎ P × R)
andOrDistr = (λ { (p , inj₁ q) → inj₁ (p , q);  --
                  (p , inj₂ r) → inj₂ (p , r) }) ,  --
             (λ { (inj₁ (p , q)) → p , inj₁ q; --
                  (inj₂ (p , r)) → p , inj₂ r }) --
-- botUnit     ⊥ ∧ P ⇔ ⊥
botUnit : {P : Set} → ⊥ × P ⇔ ⊥ --
botUnit = proj₁ , (λ ()) --
-- dupNeg      P ⇒ ¬¬P
dupNeg : {P : Set} → P → ¬ (¬ P) --
dupNeg p np = np p --
-- contraPos   P ⇒ Q ⇒ (¬Q ⇒ ¬P)
contraPos : {P Q : Set} → P → Q → (¬ Q → ¬ P) --
contraPos _ q nq p = nq q --
-- deMorg1     ¬P ∧ ¬Q ⇒ ¬(P ∨ Q)
deMorg1 : {P Q : Set} → ¬ P × ¬ Q → ¬ (P ⊎ Q) --
deMorg1 (np , nq) (inj₁ p) = np p --
deMorg1 (np , nq) (inj₂ q) = nq q --
-- deMorg2     ¬P ∨ ¬Q ⇒ ¬(P ∧ Q)
deMorg2 : {P Q : Set} → ¬ P ⊎ ¬ Q → ¬ (P × Q) --
deMorg2 (inj₁ np) (p , q) = np p --
deMorg2 (inj₂ nq) (p , q) = nq q --
\end{code}

*Exercise:* prove that the following predicates are equivalent to `exclMiddle`:

    ((P ⇒ Q) ⇒ P) ⇒ P (Peirce's Law)
    ¬¬P ⇒ P

\begin{code}
not3⇒not3' : ({A : Set} → A ⊎ ¬ A) → ({A : Set} → (¬ (¬ A) → A)) --
not3⇒not3' p {A} x with p {A} --
not3⇒not3' p x | inj₁ a  = a --
not3⇒not3' p x | inj₂ ¬a with x ¬a --
not3⇒not3' p x | inj₂ ¬a | () --

not3'⇒not3 : ({A : Set} → (¬ (¬ A) → A)) → ({A : Set} → A ⊎ ¬ A) --
not3'⇒not3 p = p (λ x → x (inj₂ (λ y → x (inj₁ y)))) --
\end{code}



Example of a constructive vs. indirect proof
============================================

We define the following: 

:    n is even ⇔ ∃k∈ℕ: n=2*k

We'd like to prove that if n is even, n² is also even.

 * constructive proof: n is even ⇒ ∃k∈ℕ: n = 2 * k ⇒ n² = (2 * k)² = 2 * (2 * k²) ⇒ n² is even. In this case we know a construction of "n² is even": there is a k' such that n = 2 * k', namely k' = 2 * (2 * k²).
 * indirect proof: suppose that n is even and n² is not even. Now ∀k∈ℕ: n * n = n² ≠ 2 * k. Because n is even, ∃l∈ℕ: n = 2 * l, hence n² = (2 * l)² = 2 * (2 * l²), so k = 2 * l² and this is a contradiction. Hence, "n² is not even" is false, and because of `exclMiddle`, n² is even. But (although we calculated it) we concluded without creating a construction of "n is even". We also had to use `exclMiddle`.

We can formalize these proofs in Agda:

\begin{code}
data even : ℕ → Set where -- definition of even
  double : (n : ℕ) → even (2 * n)

_² : ℕ → ℕ  -- definition of square
n ² = n * n

-- a helper lemma for proving a simple algebraic property
lemma : (n : ℕ) → (n + (n + 0)) * n + ((n + (n + 0)) * n + 0) ≡ (n + (n + 0)) * (n + (n + 0))
lemma = solve 1 (λ n → (n :+ (n :+ con 0)) :* n :+ ((n :+ (n :+ con 0)) :* n :+ con 0) :=
                       (n :+ (n :+ con 0)) :* (n :+ (n :+ con 0))) refl

-- a constructive proof. It is an algorithm that, given a proof of (even n), creates a proof of (even n²)
p-constructive : {n : ℕ} → even n → even (n ²)
p-constructive (double k) = subst even (lemma k) (double (2 * k * k))

-- an indirect proof: it shows that if n is even and n² is not even, we egt a contradiction
p-indirect : {n : ℕ} → even n → ¬ (even (n ²)) → ⊥
p-indirect (double k) o = o (subst even (lemma k) (double (2 * k * k)))

postulate -- we cannot prove the equivalent of exclMiddle, we have to postulate it
  ¬¬a⇒a : {A : Set} → ¬ (¬ A) → A

-- we can recover the proof using ¬¬a⇒a
p-indirect-conclusion : {n : ℕ} → even n → even (n ²)
p-indirect-conclusion p = ¬¬a⇒a (p-indirect p)
\end{code}

**********

If you can come up with a better example (eg. an indirect proof of a simple proposition not using the constructive one inside), please [let me know](http://akaposi.web.elte.hu)!
