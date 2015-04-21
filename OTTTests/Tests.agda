{-# OPTIONS --copatterns  #-}

open import Level
open import Data.Product
open import Data.Bool
open import Function
open import Relation.Binary.PropositionalEquality as P
open ≡-Reasoning
open import Relation.Binary

open import Isomorphisms

-- | Write dependent functions as Π-type to make duality between
-- inductive and coinducitve types clearer.
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
  ind   : Kind
  coind : Kind

--- | Make a type observable. An inductive type shall be represented by
---   a coproduct, whereas a coinductive type is represented by a product.
ObsTy : (I : Set) (B : I → Set) → Kind → Set
ObsTy I B ind   = Σ I B
ObsTy I B coind = Π I B

-- | Make a type testable
record Testable (A : Set) : Set₁ where
  coinductive
  field
    index : Set
    parts : index → Set
    kind : Kind
    obs : A → ObsTy index parts kind
    partsTestable : (i : index) → Testable (parts i)

open Testable public

record IsoTestable (A : Set) : Set₁ where
  field
    testable : Testable A
    obsIso : IsIso (obs testable)
open IsoTestable public

SubTests : {A : Set} → Testable A → Kind → Set

record NonTrivTest {A : Set} (T : Testable A) : Set where
  inductive
  constructor nonTrivTest
  field
    subT : SubTests T (kind T)
open NonTrivTest public

-- | Test formulae
data Test {A : Set} (T : Testable A) : Set where
  ⊤ : Test T
  ⊥ : Test T
  nonTriv : NonTrivTest T → Test T

SubTests T ind   = Π (index T) (λ i → Test (partsTestable T i))
SubTests T coind = Σ (index T) (λ i → Test (partsTestable T i))


-- | Satisfaction of subtests.
sat : {A : Set} {T : Testable A} →
      (k : Kind) → SubTests T k → ObsTy (index T) (parts T) k → Bool

-- | Test satisfaction
_⊨_ : {A : Set} {T : Testable A} → A → Test T → Bool
x ⊨ ⊤ = true
x ⊨ ⊥ = false
_⊨_ {A} {T} x (nonTriv nt) = sat (kind T) (subT nt) (obs T x)

sat ind   φs      o = cotuple (λ i y → y ⊨ app φs i) o
sat coind (i , φ) o = app o i ⊨ φ


-- | Observational equivalence: terms are equal if they satisfy the same tests.
record _≃〈_〉_ {A : Set} (x : A) (T : Testable A) (y : A) : Set₁ where
  field
    eqProof : (φ : Test T) → (x ⊨ φ ≡ y ⊨ φ)

open _≃〈_〉_ public

≡→≃ : {A : Set} → {T : Testable A} →
      {a b : A} → a ≡ b → a ≃〈 T 〉 b
≡→≃ p = record { eqProof = λ φ → cong (λ x → x ⊨ φ) p  }

≃-refl :  {A : Set} → (T : Testable A) →
          {a : A} → a ≃〈 T 〉 a
≃-refl T = record { eqProof = λ φ → refl }

≃-sym :  {A : Set} → (T : Testable A) →
         {a b : A} → a ≃〈 T 〉 b → b ≃〈 T 〉 a
≃-sym T p = record { eqProof = sym ∘ (eqProof p)  }

≃-trans :  {A : Set} → (T : Testable A) →
           {a b c : A} → a ≃〈 T 〉 b → b ≃〈 T 〉 c → a ≃〈 T 〉 c
≃-trans T p₁ p₂ =
  record { eqProof = λ φ → trans (eqProof p₁ φ) (eqProof p₂ φ) }

≃-setoid : {A : Set} → (T : Testable A) → Setoid _ _
≃-setoid {A} T = record
  { Carrier = A
  ;_≈_ = λ x y → x ≃〈 T 〉 y
  ; isEquivalence = record
    { refl = ≃-refl T
    ; sym = ≃-sym T
    ; trans = ≃-trans T }
  }

-- Most likely impossible to prove within Agda.
-- Is it consistent with the system to postulate this for _IsoTestable_ ?
-- ≃-cong :  {A B : Set} → {T₁ : Testable A} → {T₂ : Testable B} → {a b : A} →
--           (f : A → B) → a ≃〈 T₁ 〉 b → f a ≃〈 T₂ 〉 f b

-- If A is testable and there is a map B → A, then B is also testable.
comap-testable : {A B : Set} → (B → A) → Testable A → Testable B
comap-testable {A} {B} f T =
  record
  { index = index T
  ; parts = parts T
  ; kind = kind T
  ; obs = (obs T) ∘ f
  ; partsTestable = partsTestable T
  }

-- | If A is testable and A ≅ B, then B is iso-testable as well.
iso-testable : {A B : Set} → Iso B A → IsoTestable A → IsoTestable B
iso-testable {A} {B} I T =
  record
  { testable = comap-testable (Iso.iso I) (testable T)
  ; obsIso = iso-comp (Iso.indeedIso I) (obsIso T)
  }

-- | Heterogeneous
record _~〈_∥_〉_ {A B : Set} (x : A) (T : Testable A) (I : Iso B A) (y : B) : Set₁ where
  field
    eqProofH : (φ : Test T) → (x ⊨ φ ≡ (Iso.iso I y) ⊨ φ)

open _~〈_∥_〉_ public
