open import Signature
import Logic

module Model (Σ Δ : Sig) (V : Set) (Φ : Logic.Program Σ Δ V) where

open import Function
open import Data.Empty renaming (⊥ to Ø)
open import Data.Sum
open import Data.Product renaming (Σ to ∐)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Logic Σ Δ V
open import Terms Σ

-- | I-ary relations over A
Rel : Set → Set → Set₁
Rel I A = (I → A) → Set

_⊆ᵣ_ : ∀{I A} → Rel I A → Rel I A → Set
R₁ ⊆ᵣ R₂ = ∀{t} → R₁ t → R₂ t

PredInterpret : Set₁
PredInterpret = (Q : ∥ Δ ∥) → Rel (ar Δ Q) (T∞ Ø)

_⊑ᵢ_ : PredInterpret → PredInterpret → Set
I₁ ⊑ᵢ I₂ = ∀ {Q} → I₁ Q ⊆ᵣ I₂ Q

liftApp∞ : ∀ {V W} {I : Set} → Subst∞ V W → (I → T∞ V) → (I → T∞ W)
liftApp∞ σ f i = app∞ σ (f i)

_≡[_]_ : T∞ Ø → Subst∞ V Ø → T V → Set
t ≡[ σ ] s = t ~ app∞ σ (χ s)

{-
_⊨[_]_ : PredInterpret → Subst∞ V Ø → Formula → Set
I ⊨[ σ ] (inj₁ (Q , ts)) = liftApp∞ σ (χ ∘ ts) ∈ I Q
I ⊨[ σ ] (inj₂ _) = Ø
-}

_⊨[_]_ : PredInterpret → Subst∞ V Ø → Formula → Set
I ⊨[ σ ] (Q , ts) = liftApp∞ σ (χ ∘ ts) ∈ I Q

⟦_⟧ : dom Φ → PredInterpret → PredInterpret
⟦ C ⟧ I = F (get Φ C)
  where
    -- | Forward closure for inductive clauses is given by
    -- F(h ⊢μ Q'(t))(I)(Q)
    --   = {t[σ] | σ : V → Ø ∧ Q ≡ Q' ∧ ∀ P(s) ∈ h. s[σ] ∈ I(P)}.
    -- The backwards closure for coinductive clauses is, on the other hand,
    -- given by
    -- F(h ⊢ν P(s))(I)(Q) = {t[σ] | σ : V → Ø ∧ Q(t) ∈ h ∧ s ∈ I(Q)}
    F : Clause → PredInterpret
    F (h ⊢[ ind ] (Q' , pat)) Q ts =
      ∐ (Q' ≡ Q) (λ p →
      ∃ (λ σ →
        ∀ i → ts (subst _ p i) ≡[ σ ] pat i
        × (∀ j → I ⊨[ σ ] get h j)))
    F (h ⊢[ coind ] φ) Q ts =
      ∃ (λ j →
      ∐ (proj₁ (get h j) ≡ Q) (λ p →
      ∃ (λ σ →
        ∀ i → ts (subst _ p i) ≡[ σ ] proj₂ (get h j) i
        × I ⊨[ σ ] φ)))

FormInterpret : PredInterpret → Formula → Pred (Subst∞ V Ø) _
FormInterpret I (Q , ts) σ = (λ i → app∞ σ (χ (ts i))) ∈ I Q

B : (Formula → Pred (Subst∞ V Ø) _) → (Formula → Pred (Subst∞ V Ø) _)
B D F = {!!}

record ModelData : Set₁ where
  field
    preds : PredInterpret
    
