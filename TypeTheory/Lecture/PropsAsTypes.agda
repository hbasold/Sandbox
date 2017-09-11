{-# OPTIONS --without-K #-}

module PropsAsTypes where

data Σ {I : Set} (X : I → Set) : Set where
  _,_ : (i : I) → X i → Σ X

drec-Σ :  {I : Set} {X : I → Set} {A : Σ X → Set} →
          ((i : I) → (x : X i) → A (i , x)) →
          (u : Σ X) → A u
drec-Σ f (i , x) = f i x

π₁ : {I : Set} {X : I → Set} → Σ X → I
π₁ = drec-Σ (λ i x → i)

π₂ : {I : Set} {X : I → Set} → (u : Σ X) → X (π₁ u)
π₂ = drec-Σ (λ i x → x)

_×_ : Set → Set → Set
A × B = Σ {A} λ _ → B

Prop = Set

Pred : Set → Set₁
Pred A = A → Prop

Rel : Set → Set₁
Rel A = A → A → Prop

_⊆_ : {A : Set} → Pred A → Pred A → Prop
P ⊆ Q = ∀ x → P x → Q x

_⊑_ : {A : Set} → Rel A → Rel A → Prop
R ⊑ S = ∀ {x y} → R x y → S x y

_∧_ : Prop → Prop → Prop
A ∧ B = A × B

∧-elim₁ : {A₁ A₂ : Prop} → A₁ ∧ A₂ → A₁
∧-elim₁ = π₁

∧-elim₂ : {A₁ A₂ : Prop} → A₁ ∧ A₂ → A₂
∧-elim₂ = π₂

∧-intro : {A₁ A₂ : Prop} → A₁ → A₂ → A₁ ∧ A₂
∧-intro a₁ a₂ = (a₁ , a₂)

∃ : {X : Set} → (A : X → Prop) → Prop
∃ = Σ

∃-syntax : ∀ X → (X → Prop) → Prop
∃-syntax X A = ∃ A

syntax ∃-syntax X (λ x → A) = ∃[ x ∈ X ] A

∃-intro : {X : Set} {A : X → Prop} → (x : X) → A x → ∃[ x ∈ X ] (A x)
∃-intro x a = (x , a)

∃-elim :  {X : Set} {A : X → Prop} {B : Prop} →
          ((x : X) → A x → B) → ∃[ x ∈ X ] (A x) → B
∃-elim = drec-Σ

∃₂-elim :  {X Y : Set} {A : X → Prop} {B : Y → Prop} {C : Prop} →
           ((x : X) (y : Y) → A x → B y → C) →
           ∃[ x ∈ X ] (A x) → ∃[ x ∈ Y ] (B x) → C
∃₂-elim f p q = ∃-elim (λ x p' → ∃-elim (λ y q' → f x y p' q') q) p

infix 3 _⇔_

_⇔_ : Prop → Prop → Prop
A ⇔ B = (A → B) ∧ (B → A)

equivalence : {A B : Prop} → (A → B) → (B → A) → A ⇔ B
equivalence = ∧-intro

data ⊥ : Prop where
  absurd : ⊥ → ⊥

⊥-elim : {A : Prop} → ⊥ → A
⊥-elim (absurd p) = ⊥-elim p

¬ : Prop → Prop
¬ A = A → ⊥

data ⊤ : Prop where
  ∗ : ⊤

open import Data.Nat
open import Relation.Binary.PropositionalEquality as PE

IsSuc : ℕ → Set
IsSuc zero    = ⊥
IsSuc (suc _) = ⊤

zero-not-suc : ∀ n → ¬ (suc n ≡ 0)
zero-not-suc n p = subst IsSuc p ∗

-- Easier in Agda with absurd elimination
-- suc-injective : ∀ n → ¬ (suc n ≡ n)
-- suc-injective n ()

drec-≡ : {X : Set} → {C : (x y : X) → x ≡ y → Set} →
         ((x : X) → C x x refl) →
         ∀ x y → (p : x ≡ y) → C x y p
drec-≡ f x .x refl = f x
