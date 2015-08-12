{-# OPTIONS --copatterns --sized-types #-}

open import Level
open import Algebra.Structures
open import Relation.Binary
open import Algebra.FunctionProperties

module Comb (K : Set) (_≈_ : Rel K zero)
         (_+_ _⋆_ : Op₂ K) (-_ : Op₁ K) (0# 1# : K)
         (isRing : IsRing _≈_ _+_ _⋆_ -_ 0# 1#) where

open import Size
open import Function hiding (const)
open import Relation.Nullary
open import Stream
open import Data.Nat renaming (_+_ to _+ℕ_)
open import Data.Fin hiding (_+_)
open import Data.Product hiding (_×_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality as P
  using (_≡_) --; refl; sym; trans; cong; module ≡-Reasoning)

K-setoid : Setoid _ _
K-setoid = record { Carrier = K
                  ; _≈_ = _≈_
                  ; isEquivalence = IsRing.isEquivalence isRing }

open Bisim K-setoid
import Relation.Binary.EqReasoning as EqR
open EqR (K-setoid) public hiding (_≡⟨_⟩_)
--open IsEquivalence (IsRing.isEquivalence isRing)
open ∼-Reasoning renaming (begin_ to begin∼_; _∎ to _∎∼)

open IsRing isRing -- using (+-cong ; +-identity)
+-identityˡ = proj₁ +-identity
+-identityʳ = proj₂ +-identity

-- zeroʳ : RightZero 0# _⋆_
-- zeroʳ = ?

----------------------
--- Basic operators --
----------------------

const : ∀ {A} → A → Str A
hd (const x) = x
tl (const x) = const x

-- | Point-wise unary operations
pw₁ : ∀ {A i} → Op₁ A → Op₁ (Str {i} A)
hd (pw₁ f σ) = f (hd σ)
tl (pw₁ f σ) = pw₁ f (tl σ)

-- | Point-wise binary operations
pw₂ : ∀ {A i} → Op₂ A → Op₂ (Str {i} A)
hd (pw₂ f σ τ) = f (hd σ) (hd τ)
tl (pw₂ f σ τ) = pw₂ f (tl σ) (tl τ)

[_] : K → Str K
hd [ r ] = r
tl [ r ] = [ 0# ]

-- | Can, in conjunction with _×_, delay stream.
X : Str K
hd X = 0#
tl X = [ 1# ]

_⊕_ : ∀{i} → Str {i} K → Str {i} K → Str {i} K
_⊕_ = pw₂ _+_

⊝_ : ∀{i} → Str {i} K → Str {i} K
⊝_ = pw₁ -_

_×_ : ∀ {i} → Str {i} K → Str {i} K → Str {i} K
hd (σ × τ) = hd σ ⋆ hd τ
tl (σ × τ) = (tl σ × τ) ⊕ ([ hd σ ] × tl τ)

-- | We restrict attention to the case where the head is 1,
-- which is trivially invertible in any ring.
hasInv : ∀ {i} → Str {i} K → Set
hasInv σ = hd σ ≈ 1#

-- | Construct convolution inverse, if it exists.
inv : ∀ {i} → (σ : Str {i} K) → hasInv σ → Str {i} K
hd (inv σ p) = hd σ
tl (inv σ p) = ⊝ (tl σ × inv σ p)

-- | Powers of delay stream
X^_ : ℕ → Str K
X^ 0 = [ 1# ]
X^ (suc k) = X × (X^ k)

{-
record Summable (σ : Str (Str K)) : Set where
  coinductive
  field
    hd-smble : ∃ λ n → δ n (hd σ) ∼ [ 0# ]
    tl-smble : Summable (tl σ)
open Summable
-}

SummableDiag : {A : Set} (f : A → K) → Set
SummableDiag {A} f =
  ∃ λ n →
  Σ (Fin n → A) (λ g →
  (a : A) → ¬ ((f a) ≈ 0#) → ∃ λ i → a ≡ g i)

record Summable {A : Set} (f : A → Str K) : Set where
  coinductive
  field
    hd-smble : SummableDiag (hd ∘ f)
    tl-smble : Summable (tl' ∘ f)
open Summable

-- | Sum a finitely indexed family of elements of K.
-- This relies on commutativity etc. of addition in K.
sum : {n : ℕ} → (Fin n → K) → K
sum {ℕ.zero}  f = 0#
sum {ℕ.suc n} f = f Fin.zero + sum (f ∘ Fin.suc)

-- | Sum a family of streams.
∑ : ∀ {A} → (f : A → Str K) → Summable f → Str K
hd (∑ f p) =
  let (_ , g , _) = hd-smble p
  in  sum (hd ∘ f ∘ g)
tl (∑ f p) = ∑ (tl' ∘ f) (tl-smble p)

-- | Constant family of zero streams is summable
zero-summable : Summable {ℕ} (λ n → [ 0# ])
hd-smble zero-summable
  = (0 , f , q)
  where
    f : Fin 0 → ℕ
    f ()

    q : (n : ℕ) → ¬ (hd [ 0# ] ≈ 0#) → ∃ λ i → n ≡ f i
    q n p = ⊥-elim (p (IsRing.refl isRing))
tl-smble zero-summable = zero-summable

polySeq : ∀{i} → Str {i} (Str K) → Str {i} (Str K)
hd (polySeq σ) = hd σ × (X^ 0)
tl (polySeq σ) = pw₂ _×_ (polySeq (tl σ)) (const X)

polySeq₁ : Str (Str K) → (ℕ → Str K)
polySeq₁ σ = _at_ (polySeq σ)

polySeq₂ : (ℕ → Str K) → (ℕ → Str K)
polySeq₂ f = polySeq₁ (toStr f)

polySeq-summable : (σ : Str (Str K)) → Summable (polySeq₁ σ)
hd-smble (polySeq-summable σ) = q
  where
    q : SummableDiag (hd ∘ polySeq₁ σ)
    q = {!!}
tl-smble (polySeq-summable σ) = {!!}

{-
polySeq-expl : (σ : Str (Str K)) → (i : ℕ) → (polySeq σ at i) ≡ (σ at i) × (X^ i)
polySeq-expl σ zero    = refl
polySeq-expl σ (suc i) =
  polySeq σ at (ℕ.suc i)
    ≡⟨ ? ⟩
  (σ at (ℕ.suc i)) × (X × (X^ i))
    ∎
-}

-- lem : {f : ℕ → Str K} {k n : ℕ} → ¬ (polySeq f k at n) ≈ 0# → k ≡ n
-- lem = {!!}

{-
polySeq-summable-aux : {f : ℕ → Str K} →
                       (n : ℕ) → (g : ℕ → Str K) → Summable (polySeq f)
hd-smble (polySeq-summable-aux f n) = (1 , supp , {!!})
  where
    p = polySeq f

    supp : Fin 1 → ℕ
    supp Fin.zero = n
    supp (Fin.suc ())

    is-supp : (k : ℕ) → ¬ (hd (p k) ≈ 0#) → ∃ λ i → k ≡ supp i
    is-supp k q = (Fin.zero , {!!})

tl-smble (polySeq-summable-aux f n) = {!!}
-}

hd-delay-zero : (σ : Str K) → hd (X × σ) ≈ 0#
hd-delay-zero σ = zeroˡ (hd σ)
  where
    open IsNearSemiring (IsRing.isNearSemiring isRing)

⊕-cong : ∀ {i s t u v} → s ∼[ i ] t → u ∼[ i ] v → (s ⊕ u) ∼[ i ] (t ⊕ v)
hd≈ (⊕-cong s~t u~v) = +-cong (hd≈ s~t) (hd≈ u~v)
tl∼ (⊕-cong s~t u~v) = ⊕-cong (tl∼ s~t) (tl∼ u~v)

⊕-unitˡ : ∀ {i} → LeftIdentity (_∼_ {i}) [ 0# ] _⊕_
hd≈ (⊕-unitˡ s) = proj₁ +-identity (hd s)
tl∼ (⊕-unitˡ s) = ⊕-unitˡ (tl s)

⊕-comm : ∀ {i} → Commutative (_∼_ {i}) _⊕_
hd≈ (⊕-comm s t) = +-comm (hd s) (hd t)
tl∼ (⊕-comm s t) = ⊕-comm (tl s) (tl t)

⊕-unitʳ : ∀ {i} → RightIdentity (_∼_ {i}) [ 0# ] _⊕_
⊕-unitʳ s =
  s-bisim-trans
  (⊕-comm s [ 0# ])
  (⊕-unitˡ s)

×-zeroˡ : ∀ {i} → LeftZero (_∼_ {i}) [ 0# ] _×_
hd≈ (×-zeroˡ s) = zeroˡ (hd s)
  where
    open IsNearSemiring (IsRing.isNearSemiring isRing)
tl∼ (×-zeroˡ s) {j} =
  s-bisim-trans
  (⊕-cong {j} (×-zeroˡ s) (×-zeroˡ (tl s)))
  (⊕-unitˡ [ 0# ])

×-unitˡ : ∀ {i} → LeftIdentity (_∼_ {i}) [ 1# ] _×_
hd≈ (×-unitˡ s) = proj₁ *-identity (hd s)
tl∼ (×-unitˡ s) {j} =
  s-bisim-trans
  (⊕-cong {j} (×-zeroˡ s) (×-unitˡ (tl s)))
  (⊕-unitˡ (tl s))

tl-delay-id : (σ : Str K) → tl (X × σ) ∼ σ
tl-delay-id σ =
  begin∼
    tl (X × σ)
  ∼⟨ S.refl ⟩
    (tl X × σ) ⊕ ([ hd X ] × tl σ)
  ∼⟨ S.refl ⟩
    ([ 1# ] × σ) ⊕ ([ 0# ] × tl σ)
  ∼⟨ ⊕-cong (×-unitˡ σ) (×-zeroˡ (tl σ)) ⟩
    σ ⊕ [ 0# ]
  ∼⟨ ⊕-unitʳ σ ⟩
    σ
  ∎∼
  where
    module S = Setoid stream-setoid

-- | The analogue of the fundamental theorem
decomp-str : (σ : Str K) → σ ∼ ([ hd σ ] ⊕ (X × tl σ))
hd≈ (decomp-str σ) =
    begin
  hd σ
    ≈⟨ sym (+-identityʳ (hd σ)) ⟩
  hd σ + 0#
    ≈⟨ sym (+-cong refl (hd-delay-zero (tl σ))) ⟩
  hd [ hd σ ] + hd (X × tl σ)
    ≈⟨ refl ⟩
  hd ([ hd σ ] ⊕ (X × tl σ))
    ∎
tl∼ (decomp-str σ) =
  begin∼
    tl σ
  ∼⟨ S.sym (tl-delay-id (tl σ)) ⟩
    tl (X × tl σ)
  ∼⟨ S.sym (⊕-unitˡ (tl (X × tl σ))) ⟩
    [ 0# ] ⊕ tl (X × tl σ)
  ∼⟨ S.refl ⟩
    tl ([ hd σ ] ⊕ (X × tl σ))
  ∎∼
  where
    module S = Setoid stream-setoid
