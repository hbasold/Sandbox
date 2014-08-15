module FreeVarPresheaves where

open import Data.Nat as Nat
import Level
open import Categories.Category
open import Categories.Presheaf
open import Relation.Binary.Core
open import Relation.Binary
open import Function using (flip)

module DTO = DecTotalOrder Nat.decTotalOrder

data ℕ-≤-eq {n m : ℕ} : Rel (n ≤ m) Level.zero where
  triv-eq : ∀ {p q} → ℕ-≤-eq p q

ℕ-≤-eq-equivRel : ∀ {n m} → IsEquivalence (ℕ-≤-eq {n} {m})
ℕ-≤-eq-equivRel = record
  { refl = triv-eq
  ; sym = λ _ → triv-eq
  ; trans = λ _ _ → triv-eq
  }

{-
trans-assoc : ∀ {a ℓ} {A : Set a} →
  {_<_ : Rel A ℓ} →
  {trans : Transitive _<_} →
  ∀ {w x y z : A} → ∀{p : w < x} → ∀{q : x < y} → ∀{r : y < z} →
  (trans p (trans q r)) ≡ (trans (trans p q) r)
trans-assoc = {!!}
-}

ℕ-≤-eq-assoc : {m n k i : ℕ} {p : m ≤ n} {q : n ≤ k} {r : k ≤ i} →
  ℕ-≤-eq (DTO.trans p (DTO.trans q r)) (DTO.trans (DTO.trans p q) r)
ℕ-≤-eq-assoc = triv-eq

trans-resp-ℕ-≤-eq : {m n k : ℕ} {p r : n ≤ k} {q s : m ≤ n} →
  ℕ-≤-eq p r → ℕ-≤-eq q s → ℕ-≤-eq (DTO.trans q p) (DTO.trans s r)
trans-resp-ℕ-≤-eq _ _ = triv-eq

op : Category Level.zero Level.zero Level.zero
op = record
   { Obj = ℕ
   ; _⇒_ = Nat._≤_
   ; _≡_ = ℕ-≤-eq
   ; _∘_ = flip DTO.trans
   ; id = DTO.refl
   ; assoc = ℕ-≤-eq-assoc
   ; identityˡ = triv-eq
   ; identityʳ = triv-eq
   ; equiv = ℕ-≤-eq-equivRel
   ; ∘-resp-≡ = trans-resp-ℕ-≤-eq
   }

Ctx a = List (Var a)

data Var : (Γ : Ctx) → Set where
  zero : ∀{Γ}               → TyVar (Γ + 1)
  succ : ∀{Γ} (x : TyVar Γ) → TyVar (Γ + 1)
