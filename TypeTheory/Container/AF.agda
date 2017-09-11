open import Poly
open import Function
open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Product as Prod
open import Data.Sum
open import Relation.Binary.PropositionalEquality

data ℕ∞ : Set where
  fin : ℕ → ℕ∞
  ω : ℕ∞

data _<'_ : ℕ∞ → ℕ∞ → Set where
  ltSuc : (n : ℕ) → fin n <' fin (suc n)
  ltω : (n : ℕ) → fin n <' ω

z : ⊤ → ℕ∞
z _ = fin 0

suc' : ℕ∞ → ℕ∞
suc' (fin x) = fin (suc x)
suc' ω = ω

F : (ℕ∞ → Set) → (ℕ∞ → Set)
F X n = (n ≡ z tt → ⊥)
        × ((k : ℕ∞) → n ≡ suc' k → X k)
        × ((n ≡ ω) → (∃ λ k → k <' ω × X k))

A = ℕ∞ × (⊥ ⊎ ⊤ ⊎ (∃ λ k → k <' ω))
B = ⊥ ⊎ ℕ∞ ⊎ (∃ λ k → k <' ω)

f : B → A
f (inj₁ x) = (z tt , inj₁ x)
f (inj₂ (inj₁ x)) = (suc' x , inj₂ (inj₁ tt))
f (inj₂ (inj₂ y)) = (ω , inj₂ (inj₂ y))

s : B → ℕ∞
s (inj₁ x) = ⊥-elim x
s (inj₂ (inj₁ x)) = x
s (inj₂ (inj₂ y)) = proj₁ y

t : A → ℕ∞
t = proj₁

P : DPoly
P = dpoly A t B f s

-- Claim : F ≅ ⟦ P ⟧

F→P : ∀{X} n → F X n → T P X n
F→P {X} (fin zero) v = ins a (abs'' a u)
  where
    a = (z tt , inj₁ (proj₁ v refl))
    u : (b : B) → f b ≡ a → X (s b)
    u b p with b
    u b refl | inj₁ _ = ⊥-elim (proj₁ v refl)
    u b ()   | inj₂ (inj₁ x)
    u b ()   | inj₂ (inj₂ y)

F→P {X} (fin (suc k)) (_ , v , _) = ins a (abs'' a u)
  where
    a = (fin (suc k) , inj₂ (inj₁ tt))
    u : (b : B) → f b ≡ a → X (s b)
    u b p with b
    u b ()   | inj₁ x
    u b refl | inj₂ (inj₁ (fin .k)) = v (fin k) refl
    u b ()   | inj₂ (inj₁ ω)
    u b ()   | inj₂ (inj₂ y)

F→P {X} ω (_ , _ , v) = ins a (abs'' a u)
  where
    i : ∃ λ k → k <' ω
    i = Prod.map id proj₁ (v refl)

    a = (ω , inj₂ (inj₂ i))

    u : (b : B) → f b ≡ a → X (s b)
    u b p with b
    u b ()   | inj₁ x
    u b ()   | inj₂ (inj₁ x)
    u b refl | inj₂ (inj₂ _) = proj₂ (proj₂ (v refl))


P→F : ∀{X} n → T P X n → F X n
P→F (fin zero) (ins (.(fin 0) , v) x) = ? -- ({!!} , {!!})
P→F (fin (suc n)) v = {!!}
P→F ω v = {!!}
