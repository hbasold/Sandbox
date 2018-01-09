\begin{code}
{-# OPTIONS --without-K #-}
\end{code}

\begin{code}
module GreaterZero where

open import Data.Unit
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

open import CoindLog renaming (_∈'_ to _∈'-base_; _∈_ to _∈-base_)
open import Stream

Ar : List Set
Ar = [ Stream ℕ ]

STerms : Set
STerms = Terms Ar

η : Stream ℕ → STerms
η s = s , tt

SPred : Set₁
SPred = Rel Ar

SIPred : Set₁
SIPred = IRel Ar

i⊤ : IPred
i⊤ = iPred (λ _ → ⊤) (λ _ x → x)

i⊤-final : ∀ φ → (φ ⟶ i⊤)
i⊤-final φ n _ = tt

i⊤-intro : ∀ {φ} → φ ⟶ i⊤ ∧ φ
i⊤-intro n p = tt , p

-- | Simplify notation
infix 4 _∈_ _∈'_

_∈'_ : Stream ℕ → SPred → Set
s ∈' P = (η s) ∈'-base P

_∈_ : Stream ℕ → SIPred → IPred
s ∈ P = (η s) ∈-base P

-- Φ : RelT₀ Ar
-- Φ P s = hd s > 0 × (tl s ∈' P)

-- Φ-mono : Monotone Φ
-- Φ-mono P Q P⊆Q s (s₀>0 , s'∈P) = (s₀>0 , P⊆Q (tl s) s'∈P)

-- T : RelT Ar
-- T = relT Φ Φ-mono

Φ₁ : RelT₀ Ar
Φ₁ P s = 0 < hd s

Φ₁-mono : Monotone Φ₁
Φ₁-mono P Q P⊆Q s s₀>0 = s₀>0

T₁ : RelT Ar
T₁ = relT Φ₁ Φ₁-mono

Φ₂ : RelT₀ Ar
Φ₂ P s = tl s ∈' P

Φ₂-mono : Monotone Φ₂
Φ₂-mono P Q P⊆Q s s'∈P = P⊆Q (tl s) s'∈P

T₂ : RelT Ar
T₂ = relT Φ₂ Φ₂-mono

T : RelT Ar
T = T₁ ⊗ T₂

open ChainReasoning T public renaming (Seq to Tc)

_⊕_ : ∀{i} → Stream {i} ℕ → Stream {i} ℕ → Stream {i} ℕ
(s ⊕ t) .hd = s .hd + t .hd
(s ⊕ t) .tl = s .tl ⊕ t .tl

K : ℕ → Stream ℕ
K n .hd = n
K n .tl = K n

s : ∀{i} → Stream {i} ℕ
s .hd = 1
s .tl = (K 1) ⊕ s

C₀ : RelT₀ Ar
C₀ P s = ∃ λ t → P t × s ≡ (K 1) ⊕ t

C : RelT Ar
C = relT C₀ mono
  where
    mono : Monotone C₀
    mono R S R⊆S s (t , p , q) = (t , R⊆S t p , q)

CC : CompatUpTo T
CC = compatUpTo C compat
  where
    lem : ∀ t → 0 < hd t → 0 < hd ((K 1) ⊕ t)
    lem t p = ≤-step p

    lem₂ : ∀ s t → s ≡ (K 1) ⊕ t → 0 < hd t → 0 < hd s
    lem₂ s t p q = subst (λ u → 0 < hd u) (sym p) (lem t q)

    lem₃ : ∀ s t → s ≡ (K 1) ⊕ t → s .tl ≡ (K 1) ⊕ (t .tl)
    lem₃ s t p = cong (λ x → x .tl) p

    compat : (C ⊚ T) ⊑ (T ⊚ C)
    compat P s (t , (t₀>0 , t'∈P) , q) =
      (lem₂ s t q t₀>0 , (t .tl , t'∈P , lem₃ s t q))

C-∈ : s ∈ LiftT C Tc ⟶ s ∈ Tc
C-∈ = compat-∈ CC (η s)

unfold-C : s ∈ Tc ⟶ K 1 ⊕ s ∈ LiftT C Tc
unfold-C n p = (s , p , refl)

lem₈ : i⊤ ⟶ s ∈ LiftT T₁ Tc
lem₈ n _ = s≤s z≤n

lem₇ : ▶ (s ∈ Tc) ⟶ ▶ (s ∈ LiftT T₂ Tc)
lem₇ = lem₇'
  where
    lem₇' : ▶ (s ∈ Tc) ⟶ ▶ (K 1 ⊕ s ∈ Tc)
    lem₇' = _⊛_ {▶ (s ∈ Tc)}
                {▶ (K 1 ⊕ s ∈ LiftT C Tc)}
                {▶ (K 1 ⊕ s ∈ Tc)}
            (compat-∈-step CC (η (K 1 ⊕ s)))
            (mon {s ∈ Tc} {K 1 ⊕ s ∈ LiftT C Tc} unfold-C)

lem₆ : ▶ (s ∈ Tc) ⟶ ▶ (s ∈ LiftT T₁ Tc)
lem₆ = _⊛_ {▶ (s ∈ Tc)} {s ∈ LiftT T₁ Tc} {▶ (s ∈ LiftT T₁ Tc)}
       (next (s ∈ LiftT T₁ Tc))
       (_⊛_ {▶ (s ∈ Tc)} {i⊤} {s ∈ LiftT T₁ Tc}
         lem₈
         (i⊤-final (▶ (s ∈ Tc))))

lem₅ : ▶ (s ∈ Tc) ⟶ (▶ (s ∈ LiftT T₁ Tc)) ∧ (▶ (s ∈ LiftT T₂ Tc))
lem₅ = pair {▶ (s ∈ LiftT T₁ Tc)} {▶ (s ∈ LiftT T₂ Tc)} {▶ (s ∈ Tc)}
       lem₆ lem₇

lem₄ : ▶ (s ∈ Tc) ⟶ ▶ ((s ∈ LiftT T₁ Tc) ∧ (s ∈ LiftT T₂ Tc))
lem₄ = _⊛_ {▶ (s ∈ Tc)}
           {(▶ (s ∈ LiftT T₁ Tc)) ∧ (▶ (s ∈ LiftT T₂ Tc))}
           {▶ ((s ∈ LiftT T₁ Tc) ∧ (s ∈ LiftT T₂ Tc))}
       (▶-pres-∧ {s ∈ LiftT T₁ Tc} {s ∈ LiftT T₂ Tc})
       lem₅

lem₃ : ▶ (s ∈ Tc) ⟶ ▶ (s ∈ LiftT T Tc)
lem₃ = _⊛_ {▶ (s ∈ Tc)}
           {▶ ((s ∈ LiftT T₁ Tc) ∧ (s ∈ LiftT T₂ Tc))}
           {▶ (s ∈ LiftT T Tc)}
       (mon {(s ∈ LiftT T₁ Tc) ∧ (s ∈ LiftT T₂ Tc)}
            {s ∈ LiftT T Tc}
            (∈-liftT-⊗-distr T₁ T₂ Tc (η s)))
       lem₄

lem₂ : ▶ (s ∈ Tc) ⟶ (s ∈ Tc)
lem₂ = _⊛_ {▶ (s ∈ Tc)} {▶ (s ∈ LiftT T Tc)} {(s ∈ Tc)}
       (seq (η s))
       lem₃

lem₁ : i⊤ ∧ ▶ (s ∈ Tc) ⟶ (s ∈ Tc)
lem₁ = _⊛_ {i⊤ ∧ ▶ (s ∈ Tc)} {▶ (s ∈ Tc)} {(s ∈ Tc)} lem₂ (π₂ {i⊤} {▶ (s ∈ Tc)})

lem : i⊤ ⟶ ▶ (s ∈ Tc) ⇒ (s ∈ Tc)
lem = abstr {i⊤} {▶ (s ∈ Tc)} {(s ∈ Tc)} lem₁

-- Goal
thm : i⊤ ⟶ s ∈ Tc
thm = _⊛_ {_} {▶ (s ∈ Tc) ⇒ (s ∈ Tc)} {s ∈ Tc} (löb {s ∈ Tc}) lem

\end{code}
