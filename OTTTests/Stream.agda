{-# OPTIONS --copatterns --sized-types #-}

open import Level
open import Data.Product
open import Data.Bool
open import Relation.Binary.PropositionalEquality as P

record Π {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  field
    app : (x : A) → B x

open Π public

cotuple : {I C : Set} →  {B : I →  Set} →  ((i : I) →  B i →  C) →  (Σ I B →  C)
cotuple f x = f (proj₁ x) (proj₂ x)

-- | Distinguish inductive and coinductive types
data Kind : Set where
  ind : Kind
  coind : Kind

-- | Make a type observable. An inductive type shall be represented by
--   a coproduct, whereas a coinductive type is represented by a product.
data Obs (A : Set) (I : Set) (B : I → Set) : Kind → Set where
  indObs : (A → Σ I B) → Obs A I B ind
  coindObs : (A → Π I B) → Obs A I B coind

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
    indH ind refl (indObs o) = cotuple (λ i y → y ⊨ φs i) (o x)
_⊨_ {A} {T} x (coindTest p (i , φ) ) = coH (kind T) p (obs T)
  where
    coH : (k : Kind) → (k ≡ coind) → Obs A (index T) (parts T) k → Bool
    coH coind refl (coindObs o) = app (o x) i ⊨ φ

-- | Observational equivalence: terms are equal if they satisfy the same tests.
record _≃〈_〉_ {A : Set} (x : A) (T : Testable A) (y : A) : Set₁ where
  field
    eqProof : (φ : Test T) → (x ⊨ φ ≡ y ⊨ φ)

open _≃〈_〉_ public

------- Examples ---------

-- | Functions are testable if their codomain is
FunTestable : {A B : Set} → Testable B → Testable (A → B)
FunTestable {A} {B} TB =
  record
  { index = A
  ; parts = λ _ → B
  ; kind = coind
  ; obs = coindObs λ f → record { app = f }
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
