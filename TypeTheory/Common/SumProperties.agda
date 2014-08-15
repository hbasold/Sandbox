module Common.SumProperties where

open import Function as Fun
open import Data.Sum as Sum
open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open ≡-Reasoning

copair-elimˡ : {A B C : Set} {f : A → C} {g : B → C} (x : A) →
               ([ f , g ]′ ) (inj₁ x) ≡ f x
copair-elimˡ x = refl

copair-elimʳ : {A B C : Set} {f : A → C} {g : B → C} (x : B) →
               ([ f , g ]′ ) (inj₂ x) ≡ g x
copair-elimʳ x = refl

copair-sum-map-merge : {A A' B B' C : Set}
                     {f₁ : A → A'} {f₂ : B → B'} {g₁ : A' → C} {g₂ : B' → C}
                     (x : A ⊎ B) →
                     ([ g₁ , g₂ ]′ ∘ Sum.map f₁ f₂) x ≡ [ g₁ ∘ f₁ , g₂ ∘ f₂ ]′ x
copair-sum-map-merge (inj₁ x) = refl
copair-sum-map-merge (inj₂ y) = refl

copair-cong : {A B C : Set} {f f' : A → C} {g : B → C}
              (p : (x : A) → f x ≡ f' x) →
              (x : A ⊎ B) →
              [ f , g ]′ x ≡ [ f' , g ]′ x
copair-cong {A} {B} {C} {f} {f'} {g} p (inj₁ x) =
  begin
    ([ f , g ]′ (inj₁ x))
  ≡⟨ refl ⟩
    f x
  ≡⟨ p x ⟩
    f' x
  ≡⟨ refl ⟩
    [ f' , g ]′ (inj₁ x)
  ∎
copair-cong p (inj₂ y) = refl

copair-distr : {A B C D : Set} {f : A → C} {g : B → C} {h : C → D}
              (x : A ⊎ B) →
              [ h ∘ f , h ∘ g ]′ x ≡ (h ∘ [ f , g ]′) x
copair-distr (inj₁ x) = refl
copair-distr (inj₂ y) = refl
