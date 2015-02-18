-- | Stuff regarding isomorphisms and isomorphic data structures.
module Isomorphisms where

open import Function
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
open ≡-Reasoning

record IsIso {A B : Set} (f : A → B) : Set where
  field
    inv : B → A
    isLeftInv : (a : A) → inv (f a) ≡ a
    isRightInv : (b : B) → f (inv b) ≡ b

iso-comp : {A B C : Set} → {f : A → B} → {g : B → C} →
           IsIso f → IsIso g → IsIso (g ∘ f)
iso-comp {A} {B} {C} {f} {g} if ig =
  record { inv = IsIso.inv if ∘ IsIso.inv ig
         ; isLeftInv = λ a →
           begin
             (IsIso.inv if ∘ IsIso.inv ig) ((g ∘ f) a)
           ≡⟨ refl ⟩
             (IsIso.inv if (IsIso.inv ig (g (f a))))
           ≡⟨ cong (λ x → IsIso.inv if x) (IsIso.isLeftInv ig (f a)) ⟩
             (IsIso.inv if (f a))
           ≡⟨ IsIso.isLeftInv if a ⟩
             a
           ∎
         ; isRightInv = λ c →
           begin
             (g ∘ f) ((IsIso.inv if ∘ IsIso.inv ig) c)
           ≡⟨ refl ⟩
             g (f ((IsIso.inv if) ((IsIso.inv ig) c)))
           ≡⟨ cong (λ x → g x) (IsIso.isRightInv if (IsIso.inv ig c)) ⟩
             g ((IsIso.inv ig) c)
           ≡⟨ IsIso.isRightInv ig c ⟩
             c
           ∎
         }

iso-rev : {A B : Set} → {f : A → B} → (I : IsIso f) →
          IsIso (IsIso.inv I)
iso-rev {A} {B} {f} I =
  record { inv = f
         ; isLeftInv = IsIso.isRightInv I
         ; isRightInv = IsIso.isLeftInv I }

record Iso (A B : Set) : Set where
  field
    iso : A → B
    indeedIso : IsIso iso

iso-trans : {A B C : Set} → Iso A B → Iso B C → Iso A C
iso-trans I₁ I₂ =
  record { iso = Iso.iso I₂ ∘ Iso.iso I₁
         ; indeedIso = iso-comp (Iso.indeedIso I₁) (Iso.indeedIso I₂) }
