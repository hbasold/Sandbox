{-# OPTIONS --without-K #-}

module Stream where
open import Level as Level using (zero)
import Relation.Binary as BinRel
open import Relation.Binary as BinRel hiding (Setoid; Rel)
open import Relation.Binary.PropositionalEquality as PE

Setoid = BinRel.Setoid Level.zero Level.zero

open import Data.Nat using (ℕ; zero; suc)
open import PropsAsTypes

record Stream (A : Set) : Set where
  coinductive
  field
    hd  : A
    tl  : Stream A
open Stream public

coiter : {X A : Set} → (X → A × X) → (X → Stream A)
coiter c x .hd  = π₁ (c x)
coiter c x .tl  = coiter c (π₂ (c x))

δ : ∀{A} → ℕ → Stream A → Stream A
δ 0        s = s
δ (suc n)  s = δ n (s .tl)

_at_ : ∀{A} → Stream A → ℕ → A
s at n = (δ n s) .hd

module Bisim (A : Set) where

  infix 2 _~_

  record _~_ (s t : Stream A) : Prop where
    coinductive
    field
      hd≡  : s .hd  ≡  t .hd
      tl~  : s .tl  ~  t .tl
  open _~_ public

  isBisim : Rel (Stream A) → Prop
  isBisim _R_ = ∀ s t → s R t → (s .hd ≡ t .hd) ∧ (s .tl R t .tl)

  ∃-bisim→~ :  ∀ {_R_} → isBisim _R_ →
               ∀ (s t : Stream A) → s R t → s ~ t
  ∃-bisim→~ R-isBisim s t q .hd≡  = ∧-elim₁ (R-isBisim s t q)
  ∃-bisim→~ R-isBisim s t q .tl~  =
    ∃-bisim→~ R-isBisim (s .tl) (t .tl) (∧-elim₂ (R-isBisim s t q))

  bisim→ext-≡ : ∀ {s t} → s ~ t → (∀ n → s at n ≡ t at n)
  bisim→ext-≡ p zero     = p .hd≡
  bisim→ext-≡ p (suc n)  = bisim→ext-≡ (p .tl~) n

  s-bisim-refl : ∀ {s : Stream A} → s ~ s
  s-bisim-refl      .hd≡  = PE.refl
  s-bisim-refl {s}  .tl~  = s-bisim-refl {s .tl}

  s-bisim-sym : ∀ {s t : Stream A} → s ~ t → t ~ s
  s-bisim-sym p .hd≡  = PE.sym       (p .hd≡)
  s-bisim-sym p .tl~  = s-bisim-sym  (p .tl~)

  s-bisim-trans : ∀ {r s t : Stream A} → r ~ s → s ~ t → r ~ t
  s-bisim-trans p q .hd≡  = PE.trans       (p .hd≡)  (q .hd≡)
  s-bisim-trans p q .tl~  = s-bisim-trans  (p .tl~)  (q .tl~)

  stream-setoid : Setoid
  stream-setoid = record
    { Carrier = Stream A
    ; _≈_ = _~_
    ; isEquivalence = record
      { refl   = s-bisim-refl
      ; sym    = s-bisim-sym
      ; trans  = s-bisim-trans
      }
    }

  import Relation.Binary.EqReasoning as EqR

  module ~-Reasoning where
    module _ where
      open EqR (stream-setoid) public
        hiding (_≡⟨_⟩_) renaming (_≈⟨_⟩_ to _~⟨_⟩_; begin_ to begin_; _∎ to _∎)
