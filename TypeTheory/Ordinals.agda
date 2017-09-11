module Ordinals where

import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Nat using (ℕ) renaming (zero to z; suc to s)
open import Data.Empty

postulate
  ext₀ : Extensionality Level.zero Level.zero
  ext₁ : Extensionality Level.zero (Level.suc Level.zero)

data Ord : Set₁ where
  zero : Ord
  succ : Ord → Ord
  sup  : (A : Set) → (f : A → Ord) → Ord

infixl 10 _≤_

module CountableOrdinals where
  inj-ℕ-Ord : ℕ → Ord
  inj-ℕ-Ord z     = zero
  inj-ℕ-Ord (s n) = succ (inj-ℕ-Ord n)

  ω : Ord
  ω = sup ℕ inj-ℕ-Ord

  _∔_ : Ord → ℕ → Ord
  α ∔ z     = α
  α ∔ (s n) = succ (α ∔ n)

  _ẋ_ : Ord → ℕ → Ord
  α ẋ z     = zero
  α ẋ (s n) = sup ℕ (λ k → (α ẋ n) ∔ k)

  _^^_ : Ord → ℕ → Ord
  α ^^ z     = succ zero
  α ^^ (s n) = sup ℕ (λ k → (α ^^ n) ẋ k)

  ω+ : ℕ → Ord
  ω+ n = ω ∔ n

  ω× : ℕ → Ord
  ω× n = ω ẋ n

  ω^ : ℕ → Ord
  ω^ n = ω ^^ n

  ω+1≢ω : sup ℕ (succ ∘ inj-ℕ-Ord) ≡ ω → ⊥
  ω+1≢ω p = {!!}

-- This should not be provable!
-- succ-sup : ∀ A f → sup A (succ ∘ f) ≡ succ (sup A f)
-- succ-sup A f = {!!}

_+_ : Ord → Ord → Ord
α + zero    = α
α + succ β  = succ (α + β)
α + sup A f = sup A (λ x → α + f x)

zeroₗ : ∀ α → zero + α ≡ α
zeroₗ zero      = refl
zeroₗ (succ α)  = cong succ (zeroₗ α)
zeroₗ (sup A f) = cong (sup A) (ext₁ (λ x → zeroₗ (f x)))

succₗ : ∀ α β → succ α + β ≡ succ (α + β)
succₗ α zero = refl
succₗ α (succ β) = cong succ (succₗ α β)
succₗ α (sup A f) = {!!}
-- trans (cong (sup A) (ext₁ (λ x → succₗ α (f x))))
                    --       (succ-sup A (λ x → α + f x))

_≤_ : Ord → Ord → Set₁
α ≤ β = ∃ λ γ → α + γ ≡ β

≤-refl : ∀ α → α ≤ α
≤-refl α = (zero , refl)

zero-min : ∀ α → zero ≤ α
zero-min α = (α , zeroₗ α)

≤-succ : ∀ α β → α ≤ β → succ α ≤ succ β
≤-succ α β (γ , p) = (γ , trans (succₗ α γ) (cong succ p))

≤-step : ∀ α β → α ≤ β → α ≤ succ β
≤-step α β (γ , p) = (succ γ , cong succ p)

≤-sup-step : ∀ α A f → (∀ x → α ≤ f x) → α ≤ sup A f
≤-sup-step α A f p = (sup A (proj₁ ∘ p) , cong (sup A) (ext₁ (proj₂ ∘ p)))

≤-supₗ : ∀ A f β → (∀ x → f x ≤ β) → sup A f ≤ β
≤-supₗ A f β p = (sup A (proj₁ ∘ p) , {!!})
  where
    q : (x : A) → (f x + proj₁ (p x)) ≡ β
    q = proj₂ ∘ p

≤-sup : ∀ A f g → (∀ x → f x ≤ g x) → sup A f ≤ sup A g
≤-sup A f g p = (sup A (proj₁ ∘ p) , {!!}) -- cong (sup A) (ext₁ {!!}))
  where
    q : (x : A) → (f x + proj₁ (p x)) ≡ g x
    q = proj₂ ∘ p

    q' : (x : A) → (sup A f + (proj₁ ∘ p) x) ≡ g x
    q' = {!!}

lem₁ : ∀ α β → α ≤ α + β
lem₁ α zero      = ≤-refl α
lem₁ α (succ β)  = ≤-step α (α + β) (lem₁ α β)
lem₁ α (sup A f) = ≤-sup-step α A (λ x → α + f x) (λ x → lem₁ α (f x))

lem₂ : ∀ α β → β ≤ α + β
lem₂ α zero = zero-min (α + zero)
lem₂ α (succ β) = ≤-succ β (α + β) (lem₂ α β)
lem₂ α (sup A f) = ≤-sup A f (λ x → α + f x) (λ x → lem₂ α (f x))
