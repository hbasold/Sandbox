{-# OPTIONS --copatterns --sized-types #-}

open import Level
open import Data.Product
open import Data.Bool
open import Function
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
open ≡-Reasoning

open import Isomorphisms

record Π {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  field
    app : (x : A) → B x

open Π public

-- | Generalised copairing for coproducts:
-- Turn an I-indexed tuple of maps fᵢ : Bᵢ → C into a map Σ I B → C.
cotuple : {I C : Set} → {B : I → Set} → ((i : I) → B i → C) → (Σ I B → C)
cotuple f x = f (proj₁ x) (proj₂ x)

-- | Distinguish inductive and coinductive types
data Kind : Set where
  ind : Kind
  coind : Kind

-- | Make a type observable. An inductive type shall be represented by
--   a coproduct, whereas a coinductive type is represented by a product.
data Obs (A : Set) (I : Set) (B : I → Set) : Kind → Set where
  indObs : (f : A → Σ I B) → IsIso f → Obs A I B ind
  coindObs : (f : A → Π I B) → IsIso f → Obs A I B coind

-- | Make a type testable
record Testable (A : Set) : Set₁ where
  coinductive
  field
    index : Set
    parts : index → Set
    kind : Kind
    obs : Obs A index parts kind
    partsTestable : (i : index) → Testable (parts i)

open Testable public

-- | Test formulae
data Test {A : Set} (T : Testable A) : Set where
  ⊤ : Test T
  ⊥ : Test T
  indTest : (kind T ≡ ind) →
            ((i : index T) → Test (partsTestable T i)) →
            Test T
  coindTest : (kind T ≡ coind) →
              (Σ (index T) (λ i → Test (partsTestable T i))) →
              Test T

-- | Test satisfaction
_⊨_ : {A : Set} {T : Testable A} → A → Test T → Bool
x ⊨ ⊤ = true
x ⊨ ⊥ = false
_⊨_ {A} {T} x (indTest p φs) = indH (kind T) p (obs T)
  where
    indH : (k : Kind) → (k ≡ ind) → Obs A (index T) (parts T) k → Bool
    indH ind refl (indObs o _) = cotuple (λ i y → y ⊨ φs i) (o x)
_⊨_ {A} {T} x (coindTest p (i , φ) ) = coH (kind T) p (obs T)
  where
    coH : (k : Kind) → (k ≡ coind) → Obs A (index T) (parts T) k → Bool
    coH coind refl (coindObs o _) = app (o x) i ⊨ φ

-- | Observational equivalence: terms are equal if they satisfy the same tests.
record _≃〈_〉_ {A : Set} (x : A) (T : Testable A) (y : A) : Set₁ where
  field
    eqProof : (φ : Test T) → (x ⊨ φ ≡ y ⊨ φ)

open _≃〈_〉_ public

≡→≃ : {A : Set} → {T : Testable A} →
      {a b : A} → a ≡ b → a ≃〈 T 〉 b
≡→≃ p = record { eqProof = λ φ → cong (λ x → x ⊨ φ) p  }

≃-refl :  {A : Set} → (T : Testable A) →
          (a : A) → a ≃〈 T 〉 a
≃-refl T a = record { eqProof = λ φ → refl }

≃-sym :  {A : Set} → (T : Testable A) →
         (a b : A) → a ≃〈 T 〉 b → b ≃〈 T 〉 a
≃-sym T a b p = record { eqProof = sym ∘ (eqProof p)  }

≃-trans :  {A : Set} → (T : Testable A) →
           (a b c : A) → a ≃〈 T 〉 b → b ≃〈 T 〉 c → a ≃〈 T 〉 c
≃-trans T a b c p₁ p₂ =
  record { eqProof = λ φ → trans (eqProof p₁ φ) (eqProof p₂ φ) }

-- Most likely impossible to prove within Agda
-- ≃-cong :  {A B : Set} → {T₁ : Testable A} → {T₂ : Testable B} → {a b : A} →
--           (f : A → B) → a ≃〈 T₁ 〉 b → f a ≃〈 T₂ 〉 f b

-- | If A is testable and A ≅ B, then B is testable as well.
iso-testable : {A B : Set} → (T : Testable A) → (I : Iso A B) → Testable B
iso-testable {A} {B} T I =
  record
  { index = index T
  ; parts = parts T
  ; kind = kind T
  ; obs = foo (kind T) (obs T)
  ; partsTestable = partsTestable T }
  where
    foo : (k : Kind) → Obs A (index T) (parts T) k → Obs B (index T) (parts T) k
    foo ind (indObs f i) =
      indObs (f ∘ IsIso.inv (Iso.indeedIso I))
             (iso-comp (iso-rev (Iso.indeedIso I)) i)
    foo coind (coindObs f i) =
      coindObs (f ∘ IsIso.inv (Iso.indeedIso I))
               (iso-comp (iso-rev (Iso.indeedIso I)) i)

{-
≃-transport : {A B : Set} → (T : Testable A) → (I : Iso A B) →
              (x y : A) → x ≃〈 T 〉 y →
              (Iso.iso I x) ≃〈 iso-testable T I 〉 (Iso.iso I y)
≃-transport {A} {B} T₁ I x y p =
  record { eqProof = f }
  where
    T₂ = iso-testable T₁ I
    f : (φ : Test (iso-testable T₁ I)) → Iso.iso I x ⊨ φ ≡ Iso.iso I y ⊨ φ
    f ⊤ = refl
    f ⊥ = refl
    f (indTest p φs) = {!!}
      where
--        bar : (o : Obs B (index T₂) (parts T₂) ind) 
        foo : cotuple (λ i z → z ⊨ φs i) ((f ∘ IsIso.inv (Iso.indeedIso I)) x)
              ≡ cotuple (λ i z → z ⊨ φs i) ((f ∘ IsIso.inv (Iso.indeedIso I)) y)
        foo = {!!}
--        foo : (k : Kind) → (k ≡ ind) → 
    f (coindTest x₁ x₂) = {!!}
-}

-- | Heterogeneous
record _~〈_∥_〉_ {A B : Set} (x : A) (T : Testable A) (I : Iso A B) (y : A) : Set₁ where
  field
    eqProofH : (φ : Test T) → (x ⊨ φ ≡ y ⊨ φ)

open _~〈_∥_〉_ public


------- Examples ---------

-- | Functions are testable if their codomain is
FunTestable : {A B : Set} → Testable B → Testable (A → B)
FunTestable {A} {B} TB =
  record
  { index = A
  ; parts = λ _ → B
  ; kind = coind
  ; obs = coindObs (λ f → record { app = f })
                   (record { inv = app
                           ; isLeftInv = λ a → refl
                           ; isRightInv = λ b → refl })
  ; partsTestable = λ _ → TB }

-- | We get extensionality for functions under observational equivalence.
ext : {A B : Set} → (T : Testable B) →
      (f : A → B) → (g : A → B) →
      ((a : A) →  f a ≃〈 T 〉 g a) →  f ≃〈 FunTestable T 〉 g
ext {A} {B} TB f g p = record { eqProof = q }
  where
    q : (φ : Test (FunTestable TB)) → f ⊨ φ ≡ g ⊨ φ
    q ⊤ = refl
    q ⊥ = refl
    q (indTest () _)
    q (coindTest refl ( a , ψ )) = eqProof (p a) ψ
