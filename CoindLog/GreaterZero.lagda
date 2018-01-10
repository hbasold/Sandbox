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
\end{code}

We fix the arity to unary, as the example is about a predicate on streams.
\begin{code}
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
\end{code}

Simplify notation
\begin{code}
infix 4 _∈_ _∈'_

_∈'_ : Stream ℕ → SPred → Set
s ∈' P = (η s) ∈'-base P

_∈_ : Stream ℕ → SIPred → IForm
s ∈ P = (η s) ∈-base P

\end{code}

The predicate we are after expresses that a stream is greater than 0 everywhere.
This predicate can be constructed as the largest fixed point of the operator Φ
with Φ P s = hd s > 0 × (tl s ∈' P).
As such, Φ is given as a product of two operators as follows.
\begin{code}
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

\end{code}

From Φ, which is the predicate transformer underlying T, we obtain the predicate
_≻0, which expresses that a stream is greater than 0 everywhere, through the
final sequence of T.
\begin{code}
open ChainReasoning T public renaming (Seq to Tc)

infix 4 _≻0

_≻₀0 : Stream ℕ → Set
s ≻₀0 = ∀ n → IForm.form (s ∈ Tc) n

_≻0 : Stream ℕ → IForm
s ≻0 = s ∈ Tc
\end{code}

Since streams are given by a finitary functor, we obtain soundness for reasoning
on the final chain of T.
\begin{code}
soundness : ∀ {s : Stream ℕ} → s ≻₀0 → ∀ n → s at n > 0
soundness p zero     = p 1 .proj₁
soundness p (suc n)  = soundness (λ m → p (1 + m) .proj₂) n
\end{code}

Example: Stream (1, 2, 3, ...) defined as stream differential equation.
\begin{code}
_⊕_ : ∀{i} → Stream {i} ℕ → Stream {i} ℕ → Stream {i} ℕ
(s ⊕ t) .hd = s .hd + t .hd
(s ⊕ t) .tl = s .tl ⊕ t .tl

K : ℕ → Stream ℕ
K n .hd = n
K n .tl = K n

s : ∀{i} → Stream {i} ℕ
s .hd = 1
s .tl = (K 1) ⊕ s
\end{code}

Contextual closure under addition with constant one stream.
\begin{code}
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

C-∈ : s ∈ LiftT C Tc ⟶ s ≻0
C-∈ = compat-∈ CC (η s)
\end{code}

Proof that s ≻ 0.
\begin{code}
unfold-C : s ∈ Tc ⟶ K 1 ⊕ s ∈ LiftT C Tc
unfold-C n p = (s , p , refl)

lem₈ : i⊤ ⟶ s ∈ LiftT T₁ Tc
lem₈ n _ = s≤s z≤n

lem₇ : ▶ (s ≻0) ⟶ ▶ (s ∈ LiftT T₂ Tc)
lem₇ = lem₇'
  where
    lem₇' : ▶ (s ≻0) ⟶ ▶ (K 1 ⊕ s ≻0)
    lem₇' = _⊛_ {▶ (s ≻0)}
                {▶ (K 1 ⊕ s ∈ LiftT C Tc)}
                {▶ (K 1 ⊕ s ≻0)}
            (compat-∈-step CC (η (K 1 ⊕ s)))
            (mon {s ≻0} {K 1 ⊕ s ∈ LiftT C Tc} unfold-C)

lem₆ : ▶ (s ≻0) ⟶ ▶ (s ∈ LiftT T₁ Tc)
lem₆ = _⊛_ {▶ (s ≻0)} {s ∈ LiftT T₁ Tc} {▶ (s ∈ LiftT T₁ Tc)}
       (next (s ∈ LiftT T₁ Tc))
       (meta-axiom {s ∈ LiftT T₁ Tc} lem₈ (▶ (s ≻0)))

lem₅ : ▶ (s ≻0) ⟶ (▶ (s ∈ LiftT T₁ Tc)) ∧ (▶ (s ∈ LiftT T₂ Tc))
lem₅ = pair {▶ (s ∈ LiftT T₁ Tc)} {▶ (s ∈ LiftT T₂ Tc)} {▶ (s ≻0)}
       lem₆ lem₇

lem₄ : ▶ (s ≻0) ⟶ ▶ ((s ∈ LiftT T₁ Tc) ∧ (s ∈ LiftT T₂ Tc))
lem₄ = _⊛_ {▶ (s ≻0)}
           {(▶ (s ∈ LiftT T₁ Tc)) ∧ (▶ (s ∈ LiftT T₂ Tc))}
           {▶ ((s ∈ LiftT T₁ Tc) ∧ (s ∈ LiftT T₂ Tc))}
       (▶-pres-∧ {s ∈ LiftT T₁ Tc} {s ∈ LiftT T₂ Tc})
       lem₅

lem₃ : ▶ (s ≻0) ⟶ ▶ (s ∈ LiftT T Tc)
lem₃ = _⊛_ {▶ (s ≻0)}
           {▶ ((s ∈ LiftT T₁ Tc) ∧ (s ∈ LiftT T₂ Tc))}
           {▶ (s ∈ LiftT T Tc)}
       (mon {(s ∈ LiftT T₁ Tc) ∧ (s ∈ LiftT T₂ Tc)}
            {s ∈ LiftT T Tc}
            (∈-liftT-⊗-distr T₁ T₂ Tc (η s)))
       lem₄

lem₂ : ▶ (s ≻0) ⟶ (s ≻0)
lem₂ = _⊛_ {▶ (s ≻0)} {▶ (s ∈ LiftT T Tc)} {(s ≻0)}
       (seq (η s))
       lem₃

-- Goal
thm : ⊢ (s ≻0)
thm = meta-löb {s ≻0} lem₂

thm' : ∀ n → s at n > 0
thm' = soundness (meta-i⊤ {s ≻0} thm)
\end{code}
