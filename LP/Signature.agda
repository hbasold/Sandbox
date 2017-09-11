module Signature where

open import Data.Product renaming (Σ to ⨿)
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

record Sig : Set₁ where
  field
    ∥_∥ : Set
    ar : ∥_∥ → Set
open Sig public

-- | Extension of signature Σ, on objects
⟪_⟫ : Sig → Set → Set
⟪ Σ ⟫ X = ⨿ ∥ Σ ∥ λ f → (ar Σ f → X)

-- | Extension of signature Σ, on morphisms
⟪_⟫₁ : (Σ : Sig) {A B : Set} → (A → B) → ⟪ Σ ⟫ A → ⟪ Σ ⟫ B
⟪_⟫₁ Σ f (s , α) = (s , f ∘ α)

-- | Lift ⟪ Σ ⟫ to relations
sig-lift : {Σ : Sig} {X : Set} (R : X → X → Set) (x y : ⟪ Σ ⟫ X) → Set
sig-lift {Σ} R (f , α) (g , β) =
  ⨿ (f ≡ g) λ p → ∀ {i} → R (α i) (β (subst (Sig.ar Σ) p i))
