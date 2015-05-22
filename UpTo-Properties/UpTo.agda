module UpTo where

open import Level
open import Relation.Binary using (Rel; IsEquivalence)
open import Data.Product
open import Categories.Support.Equivalence
open import Categories.Category
open import Categories.2-Category
open import Categories.Functor
open import Categories.NaturalTransformation
  renaming (id to natId; _≡_ to _≡N_; setoid to natSetoid)
  hiding (_∘ˡ_; _∘ʳ_)
open import Categories.Support.EqReasoning

open import NaturalTransFacts

Cat₀ = Category zero zero zero

EndoFunctor : Cat₀ → Set zero
EndoFunctor C = Functor C C

record Endo⇒ (C₁ : Cat₀) (F₁ : EndoFunctor C₁)
             (C₂ : Cat₀) (F₂ : EndoFunctor C₂)
             : Set zero where
  field
    T : Functor C₁ C₂
    ρ : NaturalTransformation (T ∘ F₁) (F₂ ∘ T)

record UpTo⇒ {C₁ : Cat₀} {F : EndoFunctor C₁}
             {C₂ : Cat₀} {G : EndoFunctor C₂}
             (S₁ S₂ : Endo⇒ C₁ F C₂ G)
             : Set zero where
  module S₁ = Endo⇒ S₁
  module S₂ = Endo⇒ S₂
  field
    γ : NaturalTransformation S₁.T S₂.T
    -- The following diagram must commute
    -- T₁F - ρ₁ -> GT₁
    --  |            |
    --  γF         Gγ
    --  |            |
    --  v            v
    -- T₂G - ρ₂ -> GT₂
    .square : S₂.ρ ∘₁ (γ ∘ʳ F) ≡N (G ∘ˡ γ) ∘₁ S₁.ρ

record _≡U_ {C₁ : Cat₀} {C₂ : Cat₀}
            {F : EndoFunctor C₁} {G : EndoFunctor C₂}
            {T₁ T₂ : Endo⇒ C₁ F C₂ G}
            (A : UpTo⇒ T₁ T₂) (B : UpTo⇒ T₁ T₂) : Set where
  field
    ≡U-proof : UpTo⇒.γ A ≡N UpTo⇒.γ B

open _≡U_
infix 4 _≡U_

.≡U-equiv : {C₁ : Cat₀} {C₂ : Cat₀}
            {F : EndoFunctor C₁} {G : EndoFunctor C₂} →
            {A B : Endo⇒ C₁ F C₂ G} →
            IsEquivalence {A = UpTo⇒ A B} (_≡U_ {C₁} {C₂} {F} {G})
≡U-equiv =
  record
  { refl = λ {A} → record { ≡U-proof = Setoid.refl natSetoid {UpTo⇒.γ A} }
  ; sym = λ {A} {B} p → record {
        ≡U-proof = Setoid.sym natSetoid {UpTo⇒.γ A} {UpTo⇒.γ B} (≡U-proof p) }
  ; trans = λ {A} {B} {C} p₁ p₂ → record {
          ≡U-proof = Setoid.trans natSetoid {UpTo⇒.γ A} {UpTo⇒.γ B} {UpTo⇒.γ C}
                     (≡U-proof p₁) (≡U-proof p₂) }
  }

id-UpTo⇒ : {C₁ : Cat₀} {F : EndoFunctor C₁}
           {C₂ : Cat₀} {G : EndoFunctor C₂}
           {A : Endo⇒ C₁ F C₂ G} → UpTo⇒ A A
id-UpTo⇒ {C₁} {F} {C₂} {G} {A} =
  record
      { γ = natId
      ; square =
        begin
          Endo⇒.ρ A ∘₁ (natId {F = Endo⇒.T A} ∘ʳ F)
        ↓⟨ ∘₁-resp-≡
           {f = Endo⇒.ρ A} {h = Endo⇒.ρ A}
           {g = natId {F = Endo⇒.T A} ∘ʳ F}
           {i = natId {F = Endo⇒.T A ∘ F}}
           (Setoid.refl natSetoid {Endo⇒.ρ A})
           (identityNatʳ {F = Endo⇒.T A} F)
         ⟩
          Endo⇒.ρ A ∘₁ (natId {F = Endo⇒.T A ∘ F})
        ↓⟨ identity₁ʳ {X = Endo⇒.ρ A} ⟩
          Endo⇒.ρ A
        ↑⟨ identity₁ˡ {X = Endo⇒.ρ A} ⟩
          natId {F = G ∘ Endo⇒.T A} ∘₁ Endo⇒.ρ A
        ↑⟨ ∘₁-resp-≡
           {f = G ∘ˡ natId {F = Endo⇒.T A}}
           {h = natId {F = G ∘ Endo⇒.T A}}
           {g = Endo⇒.ρ A} {i = Endo⇒.ρ A}
           (identityNatˡ {F = Endo⇒.T A} G)
           (Setoid.refl natSetoid {Endo⇒.ρ A})
         ⟩
          (G ∘ˡ natId {F = Endo⇒.T A}) ∘₁ Endo⇒.ρ A
        ∎
      }
        where
          open SetoidReasoning (natSetoid {F = Endo⇒.T A ∘ F} {G ∘ Endo⇒.T A})

_•_ : {C₁ : Cat₀} {F : EndoFunctor C₁}
             {C₂ : Cat₀} {G : EndoFunctor C₂}
             {A B C : Endo⇒ C₁ F C₂ G} →
             UpTo⇒ B C → UpTo⇒ A B → UpTo⇒ A C
_•_ {F = F} {G = G} {A = A} {B} {C} g f =
  record
  { γ = γ ∘₁ φ
  ; square =
    --     AF - A.ρ -> GA
    --     |           |
    --    φF          Gφ
    --     |           |
    --     v           v
    --    BF - B.ρ -> GB
    --     |           |
    --     γF         Gγ
    --     |           |
    --     v           v
    --    CF - C.ρ -> GC
    begin
      C.ρ ∘₁ ((γ ∘₁ φ) ∘ʳ F)
    ↓⟨ ∘₁-resp-≡ʳ
       {f = C.ρ} {(γ ∘₁ φ) ∘ʳ F} {(γ ∘ʳ F) ∘₁ (φ ∘ʳ F)}
       (∘ʳ-distr-∘₁ γ φ F)
     ⟩
      C.ρ ∘₁ ((γ ∘ʳ F) ∘₁ (φ ∘ʳ F))
    ↑⟨ assoc₁ {X = (φ ∘ʳ F)} {(γ ∘ʳ F)} {C.ρ} ⟩
      (C.ρ ∘₁ (γ ∘ʳ F)) ∘₁ (φ ∘ʳ F)
    ↓⟨ ∘₁-resp-≡ˡ
       {f = C.ρ ∘₁ (γ ∘ʳ F)} {G ∘ˡ γ ∘₁ B.ρ} {φ ∘ʳ F}
       (UpTo⇒.square g)
     ⟩
      (G ∘ˡ γ ∘₁ B.ρ) ∘₁ (φ ∘ʳ F)
    ↓⟨ assoc₁ {X = (φ ∘ʳ F)} {B.ρ} {G ∘ˡ γ} ⟩
      (G ∘ˡ γ) ∘₁ (B.ρ ∘₁ (φ ∘ʳ F))
    ↓⟨ ∘₁-resp-≡ʳ
       {f = G ∘ˡ γ} {B.ρ ∘₁ (φ ∘ʳ F)} {(G ∘ˡ φ) ∘₁ A.ρ}
       (UpTo⇒.square f)
     ⟩
      (G ∘ˡ γ) ∘₁ ((G ∘ˡ φ) ∘₁ A.ρ)
    ↑⟨ assoc₁ {X = A.ρ} {G ∘ˡ φ} {G ∘ˡ γ} ⟩
      ((G ∘ˡ γ) ∘₁ (G ∘ˡ φ)) ∘₁ A.ρ
    ↑⟨ ∘₁-resp-≡ˡ
       {f = G ∘ˡ (γ ∘₁ φ)} {(G ∘ˡ γ) ∘₁ (G ∘ˡ φ)}  {A.ρ}
       (∘ˡ-distr-∘₁ G γ φ)
     ⟩
      (G ∘ˡ (γ ∘₁ φ)) ∘₁ A.ρ
    ∎
  }
  where
    module A = Endo⇒ A
    module B = Endo⇒ B
    module C = Endo⇒ C
    open SetoidReasoning (natSetoid {F = A.T ∘ F} {G ∘ C.T})
    φ : A.T ⇒ B.T
    φ = UpTo⇒.γ f
    γ : B.T ⇒ C.T
    γ = UpTo⇒.γ g

-- | Category of morphisms between endofunctors, where the morphisms
-- are certain natural transformations (see UpTo⇒).
-- This category will be the the setting in which we can talk about
-- properties of up-to techniques.
EndoMor : Σ Cat₀ (λ C → Functor C C) →
          Σ Cat₀ (λ C → Functor C C) →
          Cat₀
EndoMor (C₁ , F) (C₂ , G) =
  record
  { Obj = Endo⇒ C₁ F C₂ G
  ; _⇒_ = UpTo⇒
  ; _≡_ = _≡U_
  ; id = id-UpTo⇒
  ; _∘_ = _•_
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} →
          record { ≡U-proof = assoc₁ {X = UpTo⇒.γ f} {UpTo⇒.γ g} {UpTo⇒.γ h} }
  ; identityˡ = λ {_} {_} {f} →
              record { ≡U-proof = identity₁ˡ {X = UpTo⇒.γ f} }
  ; identityʳ = λ {_} {_} {f} →
              record { ≡U-proof = identity₁ʳ {X = UpTo⇒.γ f} }
  ; equiv = ≡U-equiv
  ; ∘-resp-≡ = λ {_} {_} {_} {f} {h} {g} {i} f≡h g≡i → record {
             ≡U-proof = ∘₁-resp-≡ {f = UpTo⇒.γ f} {UpTo⇒.γ h}
                                  {UpTo⇒.γ g} {UpTo⇒.γ i}
                                  (≡U-proof f≡h) (≡U-proof g≡i) }
  }

-- | The 2-category of endofunctors, their morphisms and UpTo⇒ as 2-cells.
-- This is the 2-category of endofunctors defined by Lenisa, Power and Watanabe.
{-
Endo : 2-Category (suc zero) zero zero zero
Endo = record
         { Obj = Σ Cat₀ (λ C → Functor C C)
         ; _⇒_ = EndoMor
         ; id = record
                { F₀ = λ _ → record { T = id ; ρ = natId }
                ; F₁ = λ _ → id-UpTo⇒
                ; identity = IsEquivalence.refl ≡U-equiv
                ; homomorphism = λ {_} {_} {_} {_} {F} → {!!}
                ; F-resp-≡ = {!!}
                }
         ; —∘— = {!!}
         ; assoc = {!!}
         ; identityˡ = {!!}
         ; identityʳ = {!!}
         }
-}
