{-# OPTIONS --sized-types #-}

module CoSig where

open import Data.Product as Prod
open import Data.Fin
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Nat
open import Size
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

---- We don't use dependencies for now.

-- record CoSigDep (I : Set) : Set₁ where
--   field
--     ∥_∥ : I → Set
--     coar : {i : I} → ∥_∥ i → Set
--     sel : {i : I} (d : ∥_∥ i) → coar d → I
-- open CoSigDep public

-- Fam : Set → Set₁
-- Fam I = I → Set

-- -- | Extension of co-signature Δ, on objects
-- ⟪_⟫ : ∀{I} → CoSigDep I → Fam I → Fam I
-- ⟪ Δ ⟫ X i = (d : ∥ Δ ∥ i) → Σ[ u ∈ coar Δ d ] (X (sel Δ d u))

record CoSig : Set₁ where
  field
    ∥_∥ : Set
    coar : ∥_∥ → Set
open CoSig public

-- | Extension of co-signature Δ, on objects
⟪_⟫ : CoSig → Set → Set
--⟪ Δ ⟫ X = (d : ∥ Δ ∥) → Σ[ u ∈ coar Δ d ] X
⟪ Δ ⟫ X = (d : ∥ Δ ∥) → (coar Δ d) × X

-- | Extension of signature Σ, on morphisms
⟪_⟫₁ : (Δ : CoSig) {A B : Set} → (A → B) → ⟪ Δ ⟫ A → ⟪ Δ ⟫ B
⟪ Δ ⟫₁ f o d = Prod.map id f (o d)

-- | Lift ⟪ Δ ⟫ to relations
cosig-lift : {Δ : CoSig} {X : Set} (R : X → X → Set) (o₁ o₂ : ⟪ Δ ⟫ X) → Set
cosig-lift {Δ} _R_ o₁ o₂ =
  ∀ d → proj₁ (o₁ d) ≡ proj₁ (o₂ d) ×
        proj₂ (o₁ d) R proj₂ (o₂ d)

record CoSig-FP (Δ : CoSig) : Set where
  coinductive
  field destr : ⟪ Δ ⟫ (CoSig-FP Δ)
open CoSig-FP public

record Str {i : Size} (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : ∀ {j : Size< i} → Str {j} A
open Str public

--- Example: Streams
Str-CoSig : Set → CoSig
Str-CoSig A = record
  { ∥_∥ = ⊤
  ; coar = λ _ → A
  }

Str' : Set → Set
Str' A = CoSig-FP (Str-CoSig A)

-- We can indeed extract a stream from stream implemented through cosignatures.
Str'-Str : ∀{A} → Str' A → Str A
hd (Str'-Str s) = proj₁ (destr s tt)
tl (Str'-Str s) = Str'-Str (proj₂ (destr s tt))

-- Example: Mealy machines
MM-CoSig : Set → Set → CoSig
MM-CoSig I O = record
  { ∥_∥ = I
  ; coar = λ _ → O
  }

MM : Set → Set → Set
MM I O = CoSig-FP (MM-CoSig I O)

-- Such a Mealy machine gives rise to a causal stream transformation.
MM-Causal : ∀{I O} → MM I O → ∀{i} → Str {i} I → Str {i} O
hd (MM-Causal m s) = proj₁ (destr m (hd s))
tl (MM-Causal m s) = MM-Causal (proj₂ (destr m (hd s))) (tl s)

--- Not quite Example: Streams with stop button
BStr-CoSig : Set → CoSig
BStr-CoSig A = record
  { ∥_∥ = ⊥ ⊎ ⊤
  ; coar = BStr-CoSig-coar
  }
  where
    BStr-CoSig-coar : ⊥ ⊎ ⊤ → Set
    BStr-CoSig-coar (inj₁ x) = ⊥-elim x
    BStr-CoSig-coar (inj₂ y) = A

BStr : Set → Set
BStr A = CoSig-FP (BStr-CoSig A)

st-ones : BStr ℕ
destr st-ones (inj₁ x) = ⊥-elim x
destr st-ones (inj₂ x) = (1 , st-ones)

-- Claim: This way of definining streams with a "stop button" renders
-- the button unusable. Thus, we only get streams back.
BStr-Str : ∀{A} → BStr A → Str A
hd (BStr-Str s) = proj₁ (destr s (inj₂ tt))
tl (BStr-Str s) = BStr-Str (proj₂ (destr s (inj₂ tt)))

Str-BStr : ∀{A} → Str A → BStr A
destr (Str-BStr s) (inj₁ x) = ⊥-elim x
destr (Str-BStr s) (inj₂ y) = (hd s , Str-BStr (tl s))

--- Example: Streams with stop button
BStr'-CoSig : Set → CoSig
BStr'-CoSig A = record
  { ∥_∥ = ⊤ ⊎ ⊤
  ; coar = BStr-CoSig-coar
  }
  where
    BStr-CoSig-coar : ⊤ ⊎ ⊤ → Set
    BStr-CoSig-coar (inj₁ x) = ⊥
    BStr-CoSig-coar (inj₂ y) = A

BStr' : Set → Set
BStr' A = CoSig-FP (BStr'-CoSig A)

-- Claim: This way of defining streams with a stop button makes any
-- such stream undefinable. Thus, the fixed point is trivial.
BStr'-triv : ∀{A} → BStr' A → ⊥
BStr'-triv s = proj₁ (destr s (inj₁ tt))

-- An extension of cosignatures that allow us to give a continuation
-- for the following states. This enables us to specify systems with,
-- for example, termination.
record CoSig₂ : Set₁ where
  field
    ∥_∥₂ : Set
    coar₂ : ∥_∥₂ → Set
    cont :  ∥_∥₂ → Set
open CoSig₂ public

-- | Extension of co-signature Δ, on objects
⟪_⟫₂ : CoSig₂ → Set → Set
⟪ Δ ⟫₂ X = (d : ∥ Δ ∥₂) → (coar₂ Δ d) × (cont Δ d → X)

record CoSig₂-FP (Δ : CoSig₂) : Set where
  coinductive
  field destr₂ : ⟪ Δ ⟫₂ (CoSig₂-FP Δ)
open CoSig₂-FP public

--- Example: Streams with stop button
BStr-CoSig₂ : Set → CoSig₂
BStr-CoSig₂ A = record
  { ∥_∥₂ = ⊤ ⊎ ⊤
  ; coar₂ = BStr-CoSig-coar
  ; cont = BStr-CoSig-cont
  }
  where
    BStr-CoSig-coar : ⊤ ⊎ ⊤ → Set
    BStr-CoSig-coar (inj₁ x) = ⊤
    BStr-CoSig-coar (inj₂ y) = A

    BStr-CoSig-cont : ⊤ ⊎ ⊤ → Set
    BStr-CoSig-cont (inj₁ x) = ⊥
    BStr-CoSig-cont (inj₂ y) = ⊤

BStr₂ : Set → Set
BStr₂ A = CoSig₂-FP (BStr-CoSig₂ A)

st-ones₂ : BStr₂ ℕ
destr₂ st-ones₂ (inj₁ tt) = (tt , ⊥-elim)
destr₂ st-ones₂ (inj₂ tt) = (1 , (λ _ → st-ones₂))
