{-# OPTIONS --copatterns  #-}

module TestsInstances where

open import Function
open import Data.Product
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality as P
open ≡-Reasoning

open import Data.Empty renaming (⊥ to Empty)
open import Data.Unit renaming (⊤ to One) hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Bool.Properties using (¬-not; T-not-≡)
open import Data.Nat hiding (_⊔_)

open import Isomorphisms
open import Tests

-- | Functions are testable if their codomain is
FunTestable : {A B : Set} → Testable B → Testable (A → B)
FunTestable {A} {B} TB =
  record
  { index = A
  ; parts = λ _ → B
  ; kind = coind
  ; obs = λ f → record { app = f }
  ; partsTestable = λ _ → TB
  }

FunIsoTestable : {A B : Set} → IsoTestable B → IsoTestable (A → B)
FunIsoTestable T =
  record
  { testable = FunTestable (testable T)
  ; obsIso = (record { inv = app
                     ; isLeftInv = λ a → refl
                     ; isRightInv = λ b → refl })
  }

-- | We get extensionality for functions under observational equivalence.
ext : {A B : Set} → (T : Testable B) →
      (f : A → B) → (g : A → B) →
      ((a : A) →  f a ≃⟨ T ⟩ g a) →  f ≃⟨ FunTestable T ⟩ g
ext {A} {B} TB f g p = record { eqProof = q }
  where
    q : (φ : Test (FunTestable TB)) → f ⊨ φ ≡ g ⊨ φ
    q ⊤ = refl
    q ⊥ = refl
    q (nonTriv (i , ψ)) = eqProof (p i) ψ

-- | Make unit type testable
⊤-testable : Testable One
index  ⊤-testable = One
parts  ⊤-testable = λ _ → One
kind   ⊤-testable = coind
obs    ⊤-testable = λ { tt  → record { app = λ x → x } }
partsTestable ⊤-testable = λ i → ⊤-testable

⊤-IsoTestable : IsoTestable One
⊤-IsoTestable =
  record
  { testable = ⊤-testable
  ; obsIso =
    record { inv = λ f → app f tt
           ; isLeftInv = λ a → refl
           ; isRightInv = λ b → refl
           }
  }

-- | Obs. equiv. is a congruence on ⊤.
≃-cong-⊤ : {A : Set} → {T : Testable A} → {x y : One} →
           (f : One → A) → x ≃⟨ ⊤-testable ⟩ y → f x ≃⟨ T ⟩ f y
≃-cong-⊤ f p = record { eqProof = λ φ → refl }

Parts-ℕ : Bool → Set
Parts-ℕ true = One
Parts-ℕ false = ℕ

rep-ℕ : ℕ → Σ Bool Parts-ℕ
rep-ℕ ℕ.zero = (true , tt)
rep-ℕ (ℕ.suc n) = (false , n)

unrep-ℕ : Σ Bool Parts-ℕ → ℕ
unrep-ℕ (true , tt) = ℕ.zero
unrep-ℕ (false , n) = ℕ.suc n

-- | Make naturals testable
ℕ-testable : Testable ℕ
index  ℕ-testable = Bool
parts  ℕ-testable = Parts-ℕ
kind   ℕ-testable = ind
obs    ℕ-testable = rep-ℕ
partsTestable ℕ-testable = λ
  { true → ⊤-testable
  ; false → ℕ-testable }

ℕ-IsoTestable : IsoTestable ℕ
ℕ-IsoTestable =
  record
  { testable = ℕ-testable
  ; obsIso =
    record { inv = unrep-ℕ
           ; isLeftInv = li
           ; isRightInv = ri
           }
  }
  where
    li : (n : ℕ) → unrep-ℕ (rep-ℕ n) ≡ n
    li ℕ.zero = refl
    li (ℕ.suc a) = refl
    ri : (x : Σ Bool Parts-ℕ) → rep-ℕ (unrep-ℕ x) ≡ x
    ri (true , tt) = refl
    ri (false , n) = refl

¬zero→suc : (n : ℕ) → n ≢ zero → ∃ (λ m → n ≡ suc m)
¬zero→suc n p with n ≟ zero
¬zero→suc zero    p | yes n=z = ⊥-elim (p n=z)
¬zero→suc (suc m) p | yes sm=z = ⊥-elim (p sm=z)
¬zero→suc zero    p | no ¬n=z = ⊥-elim (p refl)
¬zero→suc (suc n) p | no ¬n=z = n , refl

lem-tt≢ff : (a : Bool) → a ≡ true → a ≢ false
lem-tt≢ff true   _ ()
lem-tt≢ff false () _

-- | If a number is observationally equivalent to 0, then it is
-- actually 0.
lem-≃→≡-ℕ-zero : {n : ℕ} → n ≃⟨ ℕ-testable ⟩ zero → n ≡ zero
lem-≃→≡-ℕ-zero {n} p = q
  where
    -- Test to distinguish zero
    ψs : SubTests ℕ-testable ind
    ψs = record { app = λ {
        true → ⊤ ;
        false → ⊥ } }

    φ : Test ℕ-testable
    φ = nonTriv ψs

    -- n fulfils test, ...
    u : n ⊨ φ ≡ true
    u = eqProof p φ

    -- ... hence is 0.
    q : n ≡ zero
    q with n ≟ zero
    q | yes n=z = n=z
    q | no ¬n=z = ⊥-elim (lem (¬zero→suc n ¬n=z))
      where
        -- If n ≡ suc n, then we get a contradiction to u
        lem : (∃ (λ m → n ≡ suc m)) → Empty
        lem (m , q) with (n ≟ suc m)
        ... | yes n=sm = lem-tt≢ff (n ⊨ φ) u contradict
          where
            contradict : n ⊨ φ ≡ false
            contradict =
              begin
                n ⊨ φ
              ≡⟨ refl ⟩
                cotuple (λ i y → y ⊨ app ψs i) (rep-ℕ n)
              ≡⟨ cong (λ u → cotuple (λ i y → y ⊨ app ψs i) (rep-ℕ u)) n=sm ⟩
                cotuple (λ i y → y ⊨ app ψs i) (false , n)
              ≡⟨ refl ⟩
                false
              ∎
        ... | no ¬n=sm = ¬n=sm q

-- | If a number is observationally equivalent to a successor, then it is
-- actually a succesor.
lem-≃→≡-ℕ-suc : (n m : ℕ) → n ≃⟨ ℕ-testable ⟩ suc m →
       ∃ λ n' → (n ≡ suc n') × (n' ≃⟨ ℕ-testable ⟩ m)
lem-≃→≡-ℕ-suc = {!!}

-- | Observational equivalence for natural numbers implies equivalence.
≃→≡-ℕ : {n m : ℕ} → n ≃⟨ ℕ-testable ⟩ m → n ≡ m
≃→≡-ℕ {n} {zero} p = lem-≃→≡-ℕ-zero p
≃→≡-ℕ {n} {(suc m)} p with lem-≃→≡-ℕ-suc n m p
... | n' , q , p' =
  begin
    n
  ≡⟨ q ⟩
    suc n'
  ≡⟨ cong suc (≃→≡-ℕ {n'} {m} p') ⟩
    suc m
  ∎

-- | Obs. equiv. is a congruence for natural numbers.
≃-cong-ℕ : {A : Set} → {T : Testable A} → {x y : ℕ} →
           (f : ℕ → A) → x ≃⟨ ℕ-testable ⟩ y → f x ≃⟨ T ⟩ f y
≃-cong-ℕ {A} {T} {x} {y} f p = record { eqProof = q }
  where
    q : (φ : Test T) → f x ⊨ φ ≡ f y ⊨ φ
    q φ = cong (λ u → f u ⊨ φ) (≃→≡-ℕ p)
