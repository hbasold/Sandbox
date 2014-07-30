{-# OPTIONS --copatterns --sized-types #-}

open import Size
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
open ≡-Reasoning

open import Data.List using (List; module List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc)

-- Sized streams via head/tail.

record Stream {i : Size} (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : ∀ {j : Size< i} → Stream {j} A
open Stream public

-- Functoriality.

map : ∀ {i A B} (f : A → B) (s : Stream {i} A) → Stream {i} B
hd (map     f s)     = f (hd s)
tl (map {i} f s) {j} = map {j} f (tl s {j})

-- Derivative
δ : ∀{A} → ℕ → Stream A → Stream A
δ 0       s = s
δ (suc n) s = δ n (tl s)

-- Indexing
_at_ : ∀{A} → Stream A → ℕ → A
s at n = hd (δ n s)

-- Stream equality is bisimilarity
record _∼ˢ_ {A : Set} {i : Size} (s t : Stream {i} A) : Set where
  coinductive
  field
    hd≡ : hd s ≡ hd t
    tl∼ : ∀ {j : Size< i} → _∼ˢ_ {A} {j} (tl s) (tl t)
open _∼ˢ_ public

s-bisim-refl : ∀{A i} {s : Stream {i} A} → s ∼ˢ s
hd≡ s-bisim-refl           = refl
tl∼ (s-bisim-refl {A} {_} {s}) {j} = s-bisim-refl {A} {j} {tl s}

s-bisim-sym : ∀{A i} {s t : Stream {i} A} → s ∼ˢ t → t ∼ˢ s
hd≡ (s-bisim-sym                 p)     = sym (hd≡ p)
tl∼ (s-bisim-sym {A} {_} {s} {t} p) {j} =
  s-bisim-sym {A} {j} {tl s} {tl t} (tl∼ p)

s-bisim-trans : ∀{A i} {r s t : Stream {i} A} → r ∼ˢ s → s ∼ˢ t → r ∼ˢ t
hd≡ (s-bisim-trans                 p q) = trans (hd≡ p) (hd≡ q)
tl∼ (s-bisim-trans {A} {_} {r} {s} {t} p q) {j} =
  s-bisim-trans {A} {j} {tl r} {tl s} {tl t} (tl∼ p) (tl∼ q)

stream-setoid : ∀{A} → Setoid _ _
stream-setoid {A} = record
  { Carrier = Stream A
  ; _≈_ = _∼ˢ_
  ; isEquivalence = record
    { refl  = s-bisim-refl
    ; sym   = s-bisim-sym
    ; trans = s-bisim-trans
    }
  }

import Relation.Binary.EqReasoning as EqR

module ∼ˢ-Reasoning where
  module _ {A : Set} where
    open EqR (stream-setoid {A}) public
      hiding (_≡⟨_⟩_) renaming (_≈⟨_⟩_ to _∼ˢ⟨_⟩_; begin_ to beginˢ_; _∎ to _∎ˢ)

-- | As usual, bisimilarity implies equality at every index.
bisim→ext-≡ : ∀ {A} {s t : Stream A} → s ∼ˢ t → ∀ {n} → s at n ≡ t at n
bisim→ext-≡ p {zero}  = hd≡ p
bisim→ext-≡ p {suc n} = bisim→ext-≡ (tl∼ p) {n}

-- Bisimilarity for everywhere defined streams.
record _∼ˢ∞_ {A : Set} (s t : Stream A) : Set where
  coinductive
  field
    hd≡∞ : hd s ≡ hd t
    tl∼∞ : (tl s) ∼ˢ∞ (tl t)
open _∼ˢ∞_ public

s-bisim∞-refl : ∀{A} {s : Stream A} → s ∼ˢ∞ s
hd≡∞ s-bisim∞-refl           = refl
tl∼∞ (s-bisim∞-refl {A} {s}) = s-bisim∞-refl {A} {tl s}

s-bisim∞-sym : ∀{A} {s t : Stream A} → s ∼ˢ∞ t → t ∼ˢ∞ s
hd≡∞ (s-bisim∞-sym             p) = sym (hd≡∞ p)
tl∼∞ (s-bisim∞-sym {A} {s} {t} p) =
  s-bisim∞-sym {A} {tl s} {tl t} (tl∼∞ p)

s-bisim∞-trans : ∀{A} {r s t : Stream A} → r ∼ˢ∞ s → s ∼ˢ∞ t → r ∼ˢ∞ t
hd≡∞ (s-bisim∞-trans                 p q) = trans (hd≡∞ p) (hd≡∞ q)
tl∼∞ (s-bisim∞-trans {A} {r} {s} {t} p q) =
  s-bisim∞-trans {A} {tl r} {tl s} {tl t} (tl∼∞ p) (tl∼∞ q)

stream∞-setoid : ∀{A} → Setoid _ _
stream∞-setoid {A} = record
  { Carrier = Stream {∞} A
  ; _≈_ = _∼ˢ∞_
  ; isEquivalence = record
    { refl  = s-bisim∞-refl
    ; sym   = s-bisim∞-sym
    ; trans = s-bisim∞-trans
    }
  }

-- | Bisimilarity on everywhere defined streams implies "infinite" bisimilarity.
bisim→bisim∞ : ∀ {A} (s t : Stream {∞} A) → s ∼ˢ t → s ∼ˢ∞ t
hd≡∞ (bisim→bisim∞ _ _ p) = hd≡ p
tl∼∞ (bisim→bisim∞ s t p) = bisim→bisim∞ (tl s) (tl t) (tl∼ p)

-- | Proof that extensionality, that is equality at every index, implies
--   bisimilarity.
--   We cannot prove that extensional equality implies bisimilarity for every
--   size, since the solver of Agda falls back to ∞ at some points.
ext-≡→bisim∞ : ∀ {A} (s t : Stream A) → (∀ (n : ℕ) → s at n ≡ t at n) → s ∼ˢ∞ t
hd≡∞ (ext-≡→bisim∞ _ _ p) = p 0
tl∼∞ (ext-≡→bisim∞ s t p) = ext-≡→bisim∞ (tl s) (tl t) p'
  where
    p' : ∀ (n : ℕ) → (tl s) at n ≡ (tl t) at n
    p' n = p (suc n)

-- | Element repetition
repeat : ∀{A} → A → Stream A
hd (repeat a) = a
tl (repeat a) = repeat a

-- Streams and lists.

-- Prepending a list to a stream.

_++ˢ_ : ∀ {i A} → List A → Stream {i} A → Stream {i} A
[]       ++ˢ s = s
(a ∷ as) ++ˢ s = a ∷ (as ++ˢ s)

-- Taking an initial segment of a stream.

takeˢ : ∀ {A} (n : ℕ) (s : Stream A) → List A
takeˢ 0       s = []
takeˢ (suc n) s = hd s ∷ takeˢ n (tl s)

_↓_ : ∀ {A} (s : Stream A) (n : ℕ) → List A
s ↓ n = takeˢ n s

