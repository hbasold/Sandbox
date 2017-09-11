module muRec where

open import Data.Nat
open import Data.Sum
open import Relation.Binary.PropositionalEquality as PE
open import PropsAsTypes

mutual
  record D (A : Set) : Set where
    coinductive
    field
      step : Dμ A

  data Dμ (A : Set) : Set where
    now   : A   → Dμ A
    later : D A → Dμ A

open D public

coiter-D : {A X : Set} → (X → A ⊎ X) → X → D A
coiter-D c x .step with c x
... | inj₁ a  = now a
... | inj₂ x' = later (coiter-D c x')

compute-D₁ : {A X : Set} (c : X → A ⊎ X) (x : X) →
            ∀ a → c x ≡ inj₁ a → coiter-D c x .step ≡ now a
compute-D₁ c x a p with c x
compute-D₁ c x .a refl | inj₁ a = refl
compute-D₁ c x  a ()   | inj₂ y

compute-D₂ : {A X : Set} (c : X → A ⊎ X) (x : X) →
             ∀ x' → c x ≡ inj₂ x' →
                    coiter-D c x .step ≡ later (coiter-D c x')
compute-D₂ c x x' p with c x
compute-D₂ c x  x' ()   | inj₁ a
compute-D₂ c x .x' refl | inj₂ x' = refl

compute-D-inv₁ : {A X : Set} (c : X → A ⊎ X) (x : X) →
                 ∀ a → coiter-D c x .step ≡ now a → c x ≡ inj₁ a
compute-D-inv₁ c x a p with c x
compute-D-inv₁ c x .a refl | inj₁ a = refl
compute-D-inv₁ c x  a ()   | inj₂ y

compute-D-inv₂ : {A X : Set} (c : X → A ⊎ X) (x : X) →
                 ∀ x' → c x ≡ inj₂ x' →
                        coiter-D c x .step ≡ later (coiter-D c x')
compute-D-inv₂ c x x' p with c x
compute-D-inv₂ c x  x' ()   | inj₁ a
compute-D-inv₂ c x .x' refl | inj₂ x' = refl


ifIsZero_then_else_ : {A : Set} → ℕ → A → A → A
ifIsZero zero    then x else y = x
ifIsZero (suc _) then x else y = y

isZeroProof : ∀{m n k : ℕ} →
              ifIsZero m then inj₁ n else inj₂ k ≡ inj₁ n →
              m ≡ 0
isZeroProof {zero}  p = refl
isZeroProof {suc m} ()

μ-rec'-coalg : (ℕ → ℕ) → ℕ → ℕ ⊎ ℕ
μ-rec'-coalg f n = ifIsZero f n then inj₁ n else inj₂ (suc n)

μ-rec' : (ℕ → ℕ) → ℕ → D ℕ
μ-rec' f = coiter-D (μ-rec'-coalg f)

μ-rec : (ℕ → ℕ) → D ℕ
μ-rec f = μ-rec' f 0

data _↓_ {A : Set} (d : D A) (a : A) : Prop where
  stopped :              d .step ≡ now a             → d ↓ a
  delayed : {d' : D A} → d .step ≡ later d' → d' ↓ a → d ↓ a

μ-rec'-coalg-correct : (f : ℕ → ℕ) (n : ℕ) → μ-rec'-coalg f n ≡ inj₁ n → f n ≡ 0
μ-rec'-coalg-correct f n p = isZeroProof p

μ-rec'-correct : (f : ℕ → ℕ) (m n : ℕ) → (μ-rec' f m ↓ n) → f (m + n) ≡ 0
μ-rec'-correct f m n (stopped p) =
  let q = compute-D-inv₁ (μ-rec'-coalg f) m n p
  in {!!}
μ-rec'-correct f m n (delayed d' p) = {!!}

μ-rec-correct : (f : ℕ → ℕ) (n : ℕ) → (μ-rec f ↓ n) → f n ≡ 0
μ-rec-correct f n (stopped p) =
  let q = compute-D-inv₁ (μ-rec'-coalg f) 0 n p
  in μ-rec'-coalg-correct f n {!!}
μ-rec-correct f n (delayed d' p) = {!!}
