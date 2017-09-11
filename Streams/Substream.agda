-- | In this module we show that the substream relation is transitive.

open import Streams
open import Relation.Binary.PropositionalEquality as P
open import Data.Product
open import Function.Equivalence

mutual
  record F : Set where
    coinductive
    field out : Fμ

  data Fμ : Set where
    pres : F → Fμ
    drop : Fμ → Fμ

open F public

μfilter : ∀{A} → Fμ → Stream A → Stream A
filter : ∀{A} → F → Stream A → Stream A

filter x = μfilter (out x)

hd (μfilter (pres x) s) = hd s
tl (μfilter (pres x) s) = filter x (tl s)
μfilter (drop u) s = μfilter u (tl s)

comp : F → F → F
μcomp : Fμ → Fμ → Fμ

out (comp x y) = μcomp (out x) (out y)

μcomp (pres x) (pres y) = pres (comp x y)
μcomp (pres x) (drop v) = drop (μcomp (out x) v)
μcomp (drop u) v        = drop (μcomp u v)

_•_ : F → F → F
y • x = comp x y

_•μ_ : Fμ → Fμ → Fμ
v •μ u = μcomp u v

filter-comp : ∀{A} → ∀ x y (s : Stream A) →
              filter (y • x) s ~ filter y (filter x s)
μfilter-comp : ∀{A} → ∀ u v (s : Stream A) →
               μfilter (v •μ u) s ~ μfilter v (μfilter u s)

filter-comp x y s = μfilter-comp (out x) (out y) s

hd~(μfilter-comp (pres x) (pres y) s) = refl
tl~(μfilter-comp (pres x) (pres y) s) = filter-comp x y (tl s)
μfilter-comp (pres x) (drop v) s = μfilter-comp (out x) v (tl s)
-- The following cases are just the same, they need to be there for Agda to
-- reduce the definition of μcomp
μfilter-comp (drop u) (pres x) s = μfilter-comp u (pres x) (tl s)
μfilter-comp (drop u) (drop v) s = μfilter-comp u (drop v) (tl s)

_≤[_]_ : ∀{A} → Stream A → F → Stream A → Set
s ≤[ x ] t = s ~ filter x t

_≤μ[_]_ : ∀{A} → Stream A → Fμ → Stream A → Set
s ≤μ[ x ] t = s ~ μfilter x t


mutual
  record _≤_ {A : Set} (s t : Stream A) : Set where
    coinductive
    field out≤ : s ≤μ t

  data _≤μ_ {A : Set} (s t : Stream A) : Set where
    ma : hd s ≡ hd t → (tl s) ≤ (tl t) → s ≤μ t
    sk : s ≤μ (tl t) → s ≤μ t

open _≤_ public

witness : ∀{A} {s t : Stream A} → s ≤ t → F
xwitness : ∀{A} {s t : Stream A} → s ≤μ t → Fμ

out (witness p) = xwitness (out≤ p)

xwitness (ma _ t≤) = pres (witness t≤)
xwitness (sk u)    = drop (xwitness u)

impl₁ : ∀{A} {s t : Stream A} → (p : s ≤ t) → s ≤[ witness p ] t
ximpl₁ : ∀{A} {s t : Stream A} → (p : s ≤μ t) → s ≤μ[ xwitness p ] t

impl₁ {A} {s} {t} p = ximpl₁ (out≤ p)

hd~ (ximpl₁ (ma h≡ t≤)) = h≡
tl~ (ximpl₁ (ma h≡ t≤)) = impl₁ t≤
ximpl₁ (sk q) = ximpl₁ q

impl₂ : ∀{A} {s t : Stream A} (x : F) → s ≤[ x ] t → s ≤ t
ximpl₂ : ∀{A} {s t : Stream A} (u : Fμ) → s ≤μ[ u ] t → s ≤μ t

out≤ (impl₂ x p) = ximpl₂ (out x) p

ximpl₂ (pres x) p = ma (hd~ p) (impl₂ x (tl~ p))
ximpl₂ (drop u) p = sk (ximpl₂ u p)

≤⇔filter-≤ : ∀{A} (s t : Stream A) →
             s ≤ t ⇔ ∃ λ p → s ≤[ p ] t
≤⇔filter-≤ s t = equivalence (λ x → witness x , impl₁ x)
                             (λ {(x , p) → impl₂ x p})

filter-resp~ : ∀{A} {s t : Stream A} (x : F) →
               s ~ t → filter x s ~ filter x t
μfilter-resp~ : ∀{A} {s t : Stream A} (u : Fμ) →
                s ~ t → μfilter u s ~ μfilter u t

filter-resp~ x p = μfilter-resp~ (out x) p
hd~ (μfilter-resp~ (pres x) p) = hd~ p
tl~ (μfilter-resp~ (pres x) p) = filter-resp~ x (tl~ p)
μfilter-resp~ (drop u) p = μfilter-resp~ u (tl~ p)


{-
We prove transitivity of the witnessed substream relation by
r ~ filter x s
  ~ filter x (filter y t)
  ~ filter (comp x y) t

-}
≤-filter-trans : ∀{A} {r s t : Stream A} {x y} →
                 r ≤[ x ] s → s ≤[ y ] t → r ≤[ x • y ] t
≤-filter-trans {x = x} {y} p q =
  ~trans p (
    ~trans (filter-resp~ x q)
           (~sym (filter-comp y x _)))

≤-trans : ∀{A} {r s t : Stream A} →
          r ≤ s → s ≤ t → r ≤ t
≤-trans p q = impl₂ (witness p • witness q)
                    (≤-filter-trans {x = witness p}
                                    {y = witness q}
                                    (impl₁ p)
                                    (impl₁ q)
                    )

-- lem : ∀{A} {s t : Stream A} → hd s ≡ hd t → tl s ≤ tl t → t ≤μ tl s → tl t ≤μ tl s
-- lem s0≡t0 t'≤s' (ma t0≡s1 t'≤s'') with out≤ t'≤s'
-- lem s0≡t0 t'≤s' (ma t0≡s1 t'≤s'') | ma s1≡t1 s''≤t'' = ma (P.sym s1≡t1) {!!}
-- lem s0≡t0 t'≤s' (ma t0≡s1 t'≤s'') | sk p = {!!}
-- lem {s = s} s0≡t0 s'≤t' (sk p) = {!!}

-- ≤-antisym : ∀{A} {s t : Stream A} →
--             s ≤ t → t ≤ s → s ~ t
-- ≤μ-antisym : ∀{A} {s t : Stream A} →
--             s ≤μ t → t ≤μ s → s ~ t
-- ≤-antisym p q = ≤μ-antisym (out≤ p) (out≤ q)
-- hd~ (≤μ-antisym (ma hs≡ht ts≤tt) _) = hs≡ht
-- tl~ (≤μ-antisym (ma hs≡ht ts≤tt) (ma ht≡hs tt≤ts)) = ≤-antisym ts≤tt tt≤ts
-- tl~ (≤μ-antisym (ma hs≡ht ts≤tt) (sk q)) = ≤μ-antisym (out≤ ts≤tt) {!!}
-- ≤μ-antisym (sk p) q = {!!}


{-
------------------
--- Try to convince Agda that x = zip(ev(x), odd(x)) is well-defined.

even : ∀{A} → Stream A → Stream A
hd (even s) = hd s
tl (even s) = even (tl (tl s))

odd : ∀{A} → Stream A → Stream A
odd s = even (tl s)

zips : ∀{A} → Stream A → Stream A → Stream A
hd (zips s t) = hd s
tl (zips s t) = zips t (tl s)

open import Data.Nat

foo : Stream ℕ
hd foo = 0
tl foo = zips (even foo) (odd foo)

-- H : Stream ℕ → Stream ℕ → Stream ℕ
-- f : ℕ → Stream ℕ → Stream ℕ → Stream ℕ

-- H s t = f (hd t) s t

-- hd (f zero s t) = hd s
-- tl (f zero s t) = H s (tl t)
-- f (suc n) s t = f n (tl s) t
-}
