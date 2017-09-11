{-# OPTIONS --without-K #-}

module Substream (A : Set) where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE
open import PropsAsTypes
open import Stream

open Bisim A
open ~-Reasoning

mutual
  record Sel : Set where
    coinductive
    field out : Selμ

  data Selμ : Set where
    pres  : Sel → Selμ
    drop  : Selμ → Selμ

open Sel public

filterμ  : Selμ → Stream A → Stream A
filter   : Sel → Stream A → Stream A

filter x = filterμ (x .out)

filterμ (pres x) s .hd  = s .hd
filterμ (pres x) s .tl  = filter x (s .tl)
filterμ (drop u) s      = filterμ u (s .tl)

_≤[_]_ : Stream A → Sel → Stream A → Prop
s ≤[ x ] t = s ~ filter x t

_≤μ[_]_ : Stream A → Selμ → Stream A → Prop
s ≤μ[ u ] t = s ~ filterμ u t

_≤'_ : Stream A → Stream A → Prop
s ≤' t = ∃[ x ∈ Sel ] (s ≤[ x ] t)

_•_   : Sel → Sel → Sel
_•μ_  : Selμ → Selμ → Selμ

(x • y) .out = (x .out) •μ (y .out)

(pres x')  •μ (pres y')  = pres (x' • y')
(drop u')  •μ (pres y')  = drop (u' •μ (y' .out))
u          •μ (drop v')  = drop (u •μ v')

filter-hom   : ∀ x y s → filter (y • x) s ~ filter y (filter x s)
filterμ-hom  : ∀ u v s → filterμ (v •μ u) s ~ filterμ v (filterμ u s)

filter-hom x y s = filterμ-hom (x .out) (y .out) s

filterμ-hom (pres x) (pres y)  s .hd≡  = refl
filterμ-hom (pres x) (pres y)  s .tl~  = filter-hom x y (s .tl)
filterμ-hom (pres x) (drop v)  s       = filterμ-hom (x .out) v (s .tl)
filterμ-hom (drop u) (pres x)  s       = filterμ-hom u (pres x) (s .tl)
filterμ-hom (drop u) (drop v)  s       = filterμ-hom u (drop v) (s .tl)

filter-resp~   : ∀{s t} (x : Sel)  → s ~ t → filter x s ~ filter x t
filterμ-resp~  : ∀{s t} (u : Selμ) → s ~ t → filterμ u s ~ filterμ u t

filter-resp~ x p = filterμ-resp~ (x .out) p

filterμ-resp~ (pres x)  p .hd≡  = p .hd≡
filterμ-resp~ (pres x)  p .tl~  = filter-resp~ x (p .tl~)
filterμ-resp~ (drop u)  p       = filterμ-resp~ u (p .tl~)

≤-witness-trans : ∀{r s t} {x y} → r ≤[ x ] s → s ≤[ y ] t → r ≤[ x • y ] t
≤-witness-trans {r} {s} {t} {x} {y} p q =
  begin
    r
  ~⟨ p ⟩
    filter x s
  ~⟨ filter-resp~ x q ⟩
    filter x (filter y t)
  ~⟨ S.sym (filter-hom y x t) ⟩
    filter (x • y) t
  ∎
  where
    module S = Setoid stream-setoid

≤'-trans : ∀{r s t} → r ≤' s → s ≤' t → r ≤' t
≤'-trans = ∃₂-elim  (λ x y p q →
                    ∃-intro (x • y) (≤-witness-trans {x = x} {y} p q))

mutual
  record _≤_ (s t : Stream A) : Prop where
    coinductive
    field out≤ : s ≤μ t

  data _≤μ_ (s t : Stream A) : Prop where
    match : (s .hd ≡ t .hd) → (s .tl ≤ t .tl) → s ≤μ t
    skip  : (s ≤μ t .tl) → s ≤μ t

open _≤_ public

witness   : {s t : Stream A} → s ≤ t → Sel
witnessμ  : {s t : Stream A} → s ≤μ t → Selμ

witness p .out = witnessμ (p .out≤)

witnessμ (match _ t≤)  = pres (witness t≤)
witnessμ (skip u)      = drop (witnessμ u)

≤-implies-witnessed≤    : ∀{s t} → (p : s ≤ t) → s ≤[ witness p ] t
≤μ-implies-witnessed≤μ  : ∀{s t} → (p : s ≤μ t) → s ≤μ[ witnessμ p ] t

≤-implies-witnessed≤ {s} {t} p = ≤μ-implies-witnessed≤μ (p .out≤)

≤μ-implies-witnessed≤μ (match h≡ t≤) .hd≡  = h≡
≤μ-implies-witnessed≤μ (match h≡ t≤) .tl~  = ≤-implies-witnessed≤ t≤
≤μ-implies-witnessed≤μ (skip q)            = ≤μ-implies-witnessed≤μ q

≤-implies-≤' : _≤_ ⊑ _≤'_
≤-implies-≤' p = ∃-intro (witness p) (≤-implies-witnessed≤ p)

witnessed≤-implies-≤    : ∀{s t} (x : Sel) → s ≤[ x ] t → s ≤ t
witnessed≤μ-implies-≤μ  : ∀{s t} (u : Selμ) → s ≤μ[ u ] t → s ≤μ t

witnessed≤-implies-≤ x p .out≤ = witnessed≤μ-implies-≤μ (x .out) p

witnessed≤μ-implies-≤μ (pres x) p  = match (p .hd≡) (witnessed≤-implies-≤ x (p .tl~))
witnessed≤μ-implies-≤μ (drop u) p  = skip (witnessed≤μ-implies-≤μ u p)

≤'-implies-≤ : _≤'_ ⊑ _≤_
≤'-implies-≤ = ∃-elim witnessed≤-implies-≤

≤-and-≤'-equivalent : ∀ {s t} → s ≤ t ⇔ s ≤' t
≤-and-≤'-equivalent = equivalence ≤-implies-≤' ≤'-implies-≤

≤-trans : ∀{r s t} → r ≤ s → s ≤ t → r ≤ t
≤-trans p q = ≤'-implies-≤ (≤'-trans (≤-implies-≤' p) (≤-implies-≤' q))
