module NaturalTransFacts where

open import Level
open import Categories.Support.Equivalence
open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
  renaming (id to natId; _≡_ to _≡N_; setoid to natSetoid)
  hiding (_∘ˡ_; _∘ʳ_)
open import Categories.Support.EqReasoning

_⇒_ = NaturalTransformation

_∘ˡ_ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
     → {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂}
     → {F G : Functor C D}
     → (H : Functor D E) → (η : NaturalTransformation F G)
     → (H ∘ F) ⇒ (H ∘ G)
H ∘ˡ η = (natId {F = H}) ∘₀ η

_∘ʳ_ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
     → {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂}
     → {F G : Functor C D}
     → (η : NaturalTransformation F G) → (K : Functor E C)
     → (F ∘ K) ⇒ (G ∘ K)
η ∘ʳ K = η ∘₀ (natId {F = K})

.∘₁-resp-≡ˡ : ∀ {o ℓ e} {o′ ℓ′ e′}
               {D : Category o ℓ e} {E : Category o′ ℓ′ e′}
               {A B C : Functor D E}
               {f h : B ⇒ C} {g : A ⇒ B}
            → f ≡N h → f ∘₁ g ≡N h ∘₁ g
∘₁-resp-≡ˡ {f = f} {h} {g} f≡h
  = ∘₁-resp-≡ {f = f} {h} {g} {g} f≡h (Setoid.refl natSetoid {g})

.∘₁-resp-≡ʳ : ∀ {o ℓ e} {o′ ℓ′ e′}
               {D : Category o ℓ e} {E : Category o′ ℓ′ e′}
               {A B C : Functor D E}
               {f : B ⇒ C} {g i : A ⇒ B}
            → g ≡N i → f ∘₁ g ≡N f ∘₁ i
∘₁-resp-≡ʳ {f = f} {g} {i} g≡i
  = ∘₁-resp-≡ {f = f} {f} {g} {i}  (Setoid.refl natSetoid {f}) g≡i


.∘ʳ-distr-∘₁ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
             → {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂}
             → {F G H : Functor C D}
             → (β : G ⇒ H) → (α : F ⇒ G) → (K : Functor E C)
             → (β ∘₁ α) ∘ʳ K ≡N (β ∘ʳ K) ∘₁ (α ∘ʳ K)
∘ʳ-distr-∘₁ {F = F} {G} {H} β α K =
  begin
    (β ∘₁ α) ∘ʳ K
  ↓⟨ Setoid.refl natSetoid {(β ∘₁ α) ∘ʳ K} ⟩
    (β ∘₁ α) ∘₀ idK
  ↑⟨ ∘₀-resp-≡
     {f = (β ∘₁ α)} {(β ∘₁ α)} {idK ∘₁ idK} {idK}
     (Setoid.refl natSetoid {β ∘₁ α})
     (identity₁ʳ {X = idK})
   ⟩
    (β ∘₁ α) ∘₀ (idK ∘₁ idK)
  ↑⟨ interchange {α = β} {idK} {α} {idK} ⟩
    (β ∘₀ idK) ∘₁ (α ∘₀ idK)
  ↓⟨ ∘₁-resp-≡
     {f = β ∘₀ idK} {β ∘ʳ K} {α ∘₀ idK} {α ∘ʳ K}
     (Setoid.refl natSetoid {β ∘₀ idK})
     (Setoid.refl natSetoid {α ∘₀ idK})
   ⟩
    (β ∘ʳ K) ∘₁ (α ∘ʳ K)
  ∎
  where
    open SetoidReasoning (natSetoid {F = F ∘ K} {H ∘ K})
    idK = natId {F = K}

.∘ˡ-distr-∘₁ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
             → {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂}
             → {F G H : Functor C D}
             → (K : Functor D E)
             → (β : G ⇒ H) → (α : F ⇒ G)
             → K ∘ˡ (β ∘₁ α) ≡N (K ∘ˡ β) ∘₁ (K ∘ˡ α)
∘ˡ-distr-∘₁ {F = F} {G} {H} K β α =
  begin
    K ∘ˡ (β ∘₁ α)
  ↓⟨ Setoid.refl natSetoid {K ∘ˡ (β ∘₁ α)} ⟩
    idK ∘₀ (β ∘₁ α)
  ↑⟨ ∘₀-resp-≡
     {f = idK ∘₁ idK} {idK} {(β ∘₁ α)} {(β ∘₁ α)}
     (identity₁ʳ {X = idK})
     (Setoid.refl natSetoid {β ∘₁ α})
   ⟩
    (idK ∘₁ idK) ∘₀ (β ∘₁ α)
  ↑⟨ interchange {α = idK} {β} {idK} {α} ⟩
    (idK ∘₀ β) ∘₁ (idK ∘₀ α)
  ↓⟨ ∘₁-resp-≡
     {f = idK ∘₀ β} {K ∘ˡ β} {idK ∘₀ α} {K ∘ˡ α}
     (Setoid.refl natSetoid {idK ∘₀ β})
     (Setoid.refl natSetoid {idK ∘₀ α})
   ⟩
    (K ∘ˡ β) ∘₁ (K ∘ˡ α)
  ∎
  where
    open SetoidReasoning (natSetoid {F = K ∘ F} {K ∘ H})
    idK = natId {F = K}

.identityNatˡ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
              → {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂}
              → {F : Functor C D}
              → (H : Functor D E)
              → H ∘ˡ natId {F = F} ≡N natId
identityNatˡ H = identity₀ʳ {X = natId {F = H}}

.identityNatʳ : ∀ {o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂}
             → {C : Category o₀ ℓ₀ e₀} {D : Category o₁ ℓ₁ e₁} {E : Category o₂ ℓ₂ e₂}
             → {F : Functor C D}
             → (K : Functor E C)
             → natId {F = F} ∘ʳ K ≡N natId
identityNatʳ {F = F} K = identity₀ʳ {X = natId {F = F}}
