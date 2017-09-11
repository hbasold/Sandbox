{-# OPTIONS --copatterns --sized-types #-}

open import Level as Level using (zero)
open import Size
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
open ≡-Reasoning

open import Data.List using (List; module List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product renaming (map to pmap)

open import Relations

-- Sized streams via head/tail.

record Stream {i : Size} (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : ∀ {j : Size< i} → Stream {j} A
open Stream public

-- Shorthand
Str = Stream

tl' : ∀ {A} → Str A → Str A
tl' s = tl s {∞}

-- Constructor
scons : ∀{A} → A → Str A → Str A
hd (scons a s) = a
tl (scons a s) = s

-- | Corecursion
corec : ∀ {X A : Set} → (X → A) → (X → X) → (X → Str A)
hd (corec h s x) = h x
tl (corec h s x) = corec h s (s x)

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

fromStr = _at_

-- | Inverse for at
toStr : ∀ {A} → (ℕ → A) → Str A
hd (toStr f) = f 0
tl (toStr f) = toStr (λ n → f (suc n))

module Bisim (S : Setoid Level.zero Level.zero) where

  infix 2 _~_

  open Setoid S renaming (Carrier to A; isEquivalence to S-equiv)
  module SE = IsEquivalence S-equiv

  -- Stream equality is bisimilarity
  record _~_ {i : Size} (s t : Stream A) : Set where
    coinductive
    field
      hd≈ : hd s ≈ hd t
      tl~ : ∀ {j : Size< i} → _~_ {j} (tl s) (tl t)
  open _~_ public

  _~[_]_ : Stream A → Size → Stream A → Set
  s ~[ i ] t = _~_ {i} s t

  s-bisim-refl : ∀ {i} {s : Stream A} → s ~[ i ] s
  hd≈ s-bisim-refl               = SE.refl
  tl~ (s-bisim-refl {_} {s}) {j} = s-bisim-refl {j} {tl s}

  s-bisim-sym : ∀ {i} {s t : Stream A} → s ~[ i ] t → t ~[ i ] s
  hd≈ (s-bisim-sym             p)     = SE.sym (hd≈ p)
  tl~ (s-bisim-sym {_} {s} {t} p) {j} =
    s-bisim-sym {j} {tl s} {tl t} (tl~ p)

  s-bisim-trans : ∀ {i} {r s t : Stream A} →
                  r ~[ i ] s → s ~[ i ] t → r ~[ i ] t
  hd≈ (s-bisim-trans                 p q)     = SE.trans (hd≈ p) (hd≈ q)
  tl~ (s-bisim-trans {_} {r} {s} {t} p q) {j} =
    s-bisim-trans {j} {tl r} {tl s} {tl t} (tl~ p) (tl~ q)

  stream-setoid : Setoid _ _
  stream-setoid = record
    { Carrier = Stream A
    ; _≈_ = _~_
    ; isEquivalence = record
      { refl  = s-bisim-refl
      ; sym   = s-bisim-sym
      ; trans = s-bisim-trans
      }
    }

  import Relation.Binary.EqReasoning as EqR

  module ~-Reasoning where
    module _ where
      open EqR (stream-setoid) public
        hiding (_≡⟨_⟩_) renaming (_≈⟨_⟩_ to _~⟨_⟩_; begin_ to begin_; _∎ to _∎)

  -- | As usual, bisimilarity implies equality at every index.
  bisim→ext-≡ : ∀ {s t : Stream A} → s ~ t → ∀ {n} → s at n ≈ t at n
  bisim→ext-≡ p {zero}  = hd≈ p
  bisim→ext-≡ p {suc n} = bisim→ext-≡ (tl~ p) {n}

  -- | Definition of bisimulation
  isBisim : Rel (Str A) Level.zero → Set
  isBisim R =
    (s t : Str A) → R s t → (hd s ≈ hd t) × R (tl s) (tl t)

  -- | Bisimulation proof principle
  ∃-bisim→~ : ∀ {R} → isBisim R → (s t : Str A) → R s t → s ~ t
  hd≈ (∃-bisim→~ R-isBisim s t q) = proj₁ (R-isBisim s t q)
  tl~ (∃-bisim→~ R-isBisim s t q) =
    ∃-bisim→~ R-isBisim (tl s) (tl t) (proj₂ (R-isBisim s t q))

  StrRel : Set₁
  StrRel = Rel (Str A) Level.zero

  -- | Relation transformer that characterises bisimulations
  Φ : Rel (Str A) Level.zero → Rel (Str A) Level.zero
  Φ R s t = (hd s ≈ hd t) × R (tl s) (tl t)

  isBisim' : Rel (Str A) Level.zero → Set
  isBisim' R = R ⇒ Φ R

  isBisim'→isBisim : ∀ {R} → isBisim' R → isBisim R
  isBisim'→isBisim p s t q = p q

  Φ-compat : RelTrans (Str A) → Set₁
  Φ-compat F = Monotone F × (∀ {R} → F (Φ R) ⇒ Φ (F R))

  isBisim-upto : RelTrans (Str A) → Rel (Str A) Level.zero → Set
  isBisim-upto F R = R ⇒ Φ (F R)

  Φ-compat-pres-upto : {F : RelTrans (Str A)} (P : Φ-compat F) {R : StrRel} →
                       isBisim-upto F R → isBisim-upto F (F R)
  Φ-compat-pres-upto (M , P) p = P ∘ (M p)

  iterTrans : RelTrans (Str A) → ℕ → StrRel → StrRel
  iterTrans F zero R = R
  iterTrans F (suc n) R = iterTrans F n (F R)

  -- Closure of up-to technique, which will be the the bisimulation we generate from it
  bisimCls : RelTrans (Str A) → StrRel → StrRel
  bisimCls F R s t = ∃ λ n → iterTrans F n R s t

  clsIsBisim : {F : RelTrans (Str A)} (P : Φ-compat F) {R : StrRel} →
               isBisim-upto F R → isBisim' (bisimCls F R)
  clsIsBisim P p {s} {t} (zero , sRt) =
    (proj₁ (p sRt) , 1 , proj₂ (p sRt))
  clsIsBisim {F} (M , P) {R} p {s} {t} (suc n , inFIter) =
    let
      foo = clsIsBisim (M , P) {F R} (Φ-compat-pres-upto (M , P) p) (n , inFIter)
    in (proj₁ foo , (pmap suc id) (proj₂ foo))

  -- Compatible up-to techniques are sound
  compat-sound : {F : RelTrans (Str A)} (P : Φ-compat F) {R : StrRel} →
                 isBisim-upto F R → (s t : Str A) → R s t → s ~ t
  compat-sound {F} P {R} p s t sRt =
    ∃-bisim→~ (isBisim'→isBisim {bisimCls F R} (clsIsBisim P p))
    s t (0 , sRt)

  -- | Useful general up-to technique: the equivalence closure is Φ-compatible.
  equivCls-compat : Φ-compat EquivCls
  equivCls-compat = equivCls-monotone , compat
    where
      compat : {R : StrRel} → EquivCls (Φ R) ⇒ Φ (EquivCls R)
      compat (cls-incl (h≈ , tR)) = (h≈ , cls-incl tR)
      compat cls-refl             = (SE.refl , cls-refl)
      compat {R} (cls-sym p)      =
        let (h≈ , tR) = compat {R} p
        in (SE.sym h≈ , cls-sym tR)
      compat {R} (cls-trans p q) =
        let (hx≈hy , txRty) = compat {R} p
            (hy≈hz , tyRtz) = compat {R} q
        in (SE.trans hx≈hy hy≈hz , cls-trans txRty tyRtz)

-- | Element repetition
repeat : ∀{A} → A → Stream A
hd (repeat a) = a
tl (repeat a) = repeat a

-- Streams and lists.

-- Prepending a list to a stream.

_++ˢ_ : ∀ {A} → List A → Stream A → Stream A
[]       ++ˢ s = s
(a ∷ as) ++ˢ s = a ∷ (as ++ˢ s)

-- Taking an initial segment of a stream.

takeˢ : ∀ {A} (n : ℕ) (s : Stream A) → List A
takeˢ 0       s = []
takeˢ (suc n) s = hd s ∷ takeˢ n (tl s)

_↓_ : ∀ {A} (s : Stream A) (n : ℕ) → List A
s ↓ n = takeˢ n s
