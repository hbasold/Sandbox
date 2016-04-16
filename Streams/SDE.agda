{-# OPTIONS --copatterns --sized-types #-}

module SDE where

open import Size
open import Function
open import Data.Product as Prod renaming (Σ to ⨿)
open import Data.Sum as Sum

open import Streams

-- | Signatures
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

-- | Terms over a given signature together with some basic operations.
module Terms (Σ : Sig) where

  -- | Terms built from the signature Σ with variables in V.
  data T (V : Set) : Set where
    sup : ⟪ Σ ⟫ (T V) ⊎ V → T V

  -- | Recursion on terms.
  rec : ∀{V X} → (f : ⟪ Σ ⟫ X ⊎ V → X) → T V → X
  rec f (sup (inj₁ (s , α))) = f (inj₁ (s , λ i → rec f (α i)))
  rec f (sup (inj₂ y))       = f (inj₂ y)

  -- | Functor T, on morphisms
  T₁ : ∀ {V W} → (V → W) → T V → T W
  T₁ f = rec (sup ∘ Sum.map id f)

  -- | Injection of variables into terms.
  η : ∀{V} → V → T V
  η = sup ∘ inj₂

-- | Interpretation of SDEs that use the given signature and set of variables.
module SDE-Impl (Σ : Sig) (X : Set) where

  open Terms Σ

  -- | Variables are streams, their derivatives or their output
  V : Set
  V = X ⊎ X -- ⊎ X

  -- | An SDE consists of an assignment of outputs and terms for
  -- each symbol in the signature. Note that both output and the
  -- terms may depend on the outputs of the arguments of the corresponding
  -- symbol.
  SDE : Set → Set
  SDE A = (f : ∥ Σ ∥) → ((ar Σ f → A) → A) × ((ar Σ f → A) → T V)

  -- | Interpretation of terms over the symbols defined by the given SDE
  -- as streams.
  ⟦_⟧₁ : ∀ {A} → SDE A → ((f : ∥ Σ ∥) → ar Σ f → X) → T V →
         ∀{i} → (X → Stream {i} A) → ∀ {j : Size< i} → Stream {j} A

  -- | Interpretation of symbols defined by the given SDE as streams.
  ⟦_⟧ : ∀ {A} → SDE A → ((f : ∥ Σ ∥) → ar Σ f → X) → (f : ∥ Σ ∥) →
        ∀{i} → (X → Stream {i} A) → Stream {i} A
  hd (⟦ E ⟧ vars f vals) = f-out (hd ∘ vals ∘ vars f)
    where f-out = proj₁ (E f)
  tl (⟦ E ⟧ vars f vals) = ⟦ E ⟧₁ vars (f-step (hd ∘ vals ∘ vars f)) vals
    where f-step = proj₂ (E f)

  ⟦ E ⟧₁ vars (sup (inj₁ (f , α)))  vals = ⟦ E ⟧ vars f (λ x → tl (vals x))
  ⟦ E ⟧₁ vars (sup (inj₂ (inj₁ x))) vals = vals x
  ⟦ E ⟧₁ vars (sup (inj₂ (inj₂ x))) vals = tl (vals x)
