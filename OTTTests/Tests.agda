{-# OPTIONS --copatterns --sized-types #-}

{- | The purpose of this module is to demonstrate how observational type theory
  can be implemented for arbitrary types in Agda through the use of tests
  and a corresponding bisimulation proof method.

  To use the equivalence for a type A, the type has to be made _testable_ by
  creating an instance of Testable for it, see the accompanying module
  TestsInstances. Such an instance effectively encodes A as inductive or
  coinductive type, by giving an observation map to a coproduct of product
  of components of A. For now, we do not pose any restrictions on this encoding,
  hence it can be used to induce trivial equivalences.

  Using such an instance of Testable for A, we can define _tests_ and
  _observational equivalence_ for A. Moreover, we give a bisimulation proof
  method and prove its soundness.
-}
module Tests where

open import Size
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

SubTests : {l : Size} → {A : Set} → Testable A → Kind → Set

-- | Test formulae
data Test {i : Size} {A : Set} (T : Testable A) : Set where
  ⊤ : Test T
  ⊥ : Test T
  nonTriv : {j : Size< i} → SubTests {j} T (kind T) → Test {i} {A} T

SubTests {l} T ind   = Π (index T) (λ i → Test {l} (partsTestable T i))
SubTests {l} T coind = Σ (index T) (λ i → Test {l} (partsTestable T i))


-- | Satisfaction of subtests.
sat : {A : Set} {T : Testable A} {l : Size} →
      (k : Kind) → SubTests {l} T k → ObsTy (index T) (parts T) k → Bool

-- | Test satisfaction
_⊨_ : {A : Set} {T : Testable A} → A → Test T → Bool
x ⊨ ⊤ = true
x ⊨ ⊥ = false
_⊨_ {A} {T} x (nonTriv nt) = sat (kind T) nt (obs T x)

sat ind   φs      o = cotuple (λ i y → y ⊨ app φs i) o
sat coind (i , φ) o = app o i ⊨ φ


-- | Observational equivalence: terms are equal if they satisfy the same tests.
record _≃⟨_⟩_ {A : Set} (x : A) (T : Testable A) (y : A) : Set₁ where
  field
    eqProof : (φ : Test T) → (x ⊨ φ ≡ y ⊨ φ)

open _≃⟨_⟩_ public

≡→≃ : {A : Set} → {T : Testable A} →
      {a b : A} → a ≡ b → a ≃⟨ T ⟩ b
≡→≃ p = record { eqProof = λ φ → cong (λ x → x ⊨ φ) p  }

≃-refl :  {A : Set} → (T : Testable A) →
          {a : A} → a ≃⟨ T ⟩ a
≃-refl T = record { eqProof = λ φ → refl }

≃-sym :  {A : Set} → (T : Testable A) →
         {a b : A} → a ≃⟨ T ⟩ b → b ≃⟨ T ⟩ a
≃-sym T p = record { eqProof = sym ∘ (eqProof p)  }

≃-trans :  {A : Set} → (T : Testable A) →
           {a b c : A} → a ≃⟨ T ⟩ b → b ≃⟨ T ⟩ c → a ≃⟨ T ⟩ c
≃-trans T p₁ p₂ =
  record { eqProof = λ φ → trans (eqProof p₁ φ) (eqProof p₂ φ) }

≃-setoid : {A : Set} → (T : Testable A) → Setoid _ _
≃-setoid {A} T = record
  { Carrier = A
  ;_≈_ = λ x y → x ≃⟨ T ⟩ y
  ; isEquivalence = record
    { refl = ≃-refl T
    ; sym = ≃-sym T
    ; trans = ≃-trans T }
  }

-- Most likely impossible to prove within Agda.
-- Is it consistent with the system to postulate this for _IsoTestable_ ?
-- ≃-cong :  {A B : Set} → {T₁ : Testable A} → {T₂ : Testable B} → {a b : A} →
--           (f : A → B) → a ≃⟨ T₁ ⟩ b → f a ≃⟨ T₂ ⟩ f b

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
record _~⟨_∥_⟩_ {A B : Set}
                (x : A) (T : Testable A) (I : Iso B A) (y : B) : Set₁ where
  field
    eqProofH : (φ : Test T) → (x ⊨ φ ≡ (Iso.iso I y) ⊨ φ)

open _~⟨_∥_⟩_ public

-- | Helper to match on Kind in construction of ≈.
≈-Proof : {A : Set} →
          (k : Kind) →
          (T : Testable A) →
          (A → ObsTy (index T) (parts T) k) →
          A → A → Set

-- | Bisimilarity induced from testable types.
record _≈⟨_⟩_ {A : Set} (x : A) (T : Testable A) (y : A) : Set where
  coinductive
  field
    proof : ≈-Proof (kind T) T (obs T) x y
open _≈⟨_⟩_ public

-- | Helper to fiddle around with index in construction of IndProof.
ResolveIdx : {A : Set} → (T : Testable A) →
             (i : index T) → (r s : ObsTy (index T) (parts T) ind) →
             proj₁ r ≡ i → proj₁ s ≡ i → Set
ResolveIdx T i (.i , x') (.i , y') refl refl = x' ≈⟨ partsTestable T i ⟩ y'

-- | Proofs of bisimilarity on inductive types.
record IndProof {A : Set}
  (T : Testable A)
  (o : A → ObsTy (index T) (parts T) ind)
  (x y : A) : Set where
  coinductive
  field
    which : index T
    eqIndex₁ : proj₁ (o x) ≡ which
    eqIndex₂ : proj₁ (o y) ≡ which
    eqTrans : ResolveIdx T which (o x) (o y) eqIndex₁ eqIndex₂
open IndProof public

-- | Proofs of bisimilarity on coinductive types.
record CoindProof {A : Set}
  (T : Testable A)
  (o : A → ObsTy (index T) (parts T) coind)
  (x y : A) : Set where
  coinductive
  field
    eqStep : (i : index T) → app (o x) i ≈⟨ partsTestable T i ⟩ app (o y) i
open CoindProof public

≈-Proof ind   = IndProof
≈-Proof coind = CoindProof

-- | Lemma for induction to prove soundness of bisimilarity
lem-≈→≃-testInduct : {j : Size} {A : Set} → (T : Testable A) → (x y : A) →
                     x ≈⟨ T ⟩ y → (φ : Test {j} T) → x ⊨ φ ≡ y ⊨ φ
lem-≈→≃-testInduct _ _ _ _ ⊤ = refl
lem-≈→≃-testInduct _ _ _ _ ⊥ = refl
lem-≈→≃-testInduct {j} {A} T x y x≈y (nonTriv {l} nt)
  = matchKind (kind T) nt (obs T) (proof x≈y)
  where

    matchKind : (k : Kind) →
           (nt : SubTests {l} T k) →
           (o : A → ObsTy (index T) (parts T) k) →
           ≈-Proof k T o x y →
           sat k nt (o x) ≡ sat k nt (o y)
    matchKind ind   nt o p
      = refine (which p) (o x) (o y) (eqIndex₁ p) (eqIndex₂ p) (eqTrans p)
      where
        --| Do pattern matching on IndProof
        refine :  (i : index T) → (r s : ObsTy (index T) (parts T) ind) →
                  (eqP₁ : proj₁ r ≡ i) → (eqP₂ : proj₁ s ≡ i) →
                  ResolveIdx T i r s eqP₁ eqP₂ →
                  (proj₂ r) ⊨ app nt (proj₁ r) ≡ (proj₂ s) ⊨ app nt (proj₁ s)
        refine i (.i , x') (.i , y') refl refl p'
          = lem-≈→≃-testInduct (partsTestable T i) x' y' p' (app nt i)
    matchKind coind nt o p
      = lem-≈→≃-testInduct (partsTestable T i) x' y' (eqStep p i) ψ
      where
        i : index T
        i = proj₁ nt
        ψ = proj₂ nt
        x' = app (o x) i
        y' = app (o y) i

-- | Bisimulation proofs are sound for observational equivalence.
≈→≃ : {A : Set} → (T : Testable A) → (x y : A) →
      x ≈⟨ T ⟩ y → x ≃⟨ T ⟩ y
≈→≃ T x y x≈y = record { eqProof = lem-≈→≃-testInduct T x y x≈y }

{-
≃→≈ : {A : Set} → (T : Testable A) → (x y : A) →
      x ≃⟨ T ⟩ y → x ≈⟨ T ⟩ y
≃→≈ {A} T x y x≃y = record { proof = matchKind (kind T) (obs T) }
  where
    matchKind : (k : Kind) →
                (o : A → ObsTy (index T) (parts T) k) →
                ≈-Proof k T o x y
    matchKind ind o = {!!}
    matchKind coind o = {!!}
-}
