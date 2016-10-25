-- | In this module we show that the substream relation is transitive.

open import Streams
open import Relation.Binary.PropositionalEquality as P
open import Data.Product
open import Function.Equivalence

mutual
  record W : Set where
    coinductive
    field out : Wμ

  data Wμ : Set where
    pres : W → Wμ
    drop : Wμ → Wμ

open W public

comp : W → W → W
xcomp : Wμ → Wμ → Wμ

out (comp x y) = xcomp (out x) (out y)

xcomp (pres x') (pres y') = pres (comp  x' y')
xcomp (drop u') (pres y') = drop (xcomp u' (out y'))
xcomp u      (drop v') = drop (xcomp u v')

xfilter : ∀{A} → Wμ → Stream A → Stream A

filter : ∀{A} → W → Stream A → Stream A
filter x = xfilter (out x)

hd (xfilter (pres x) s) = hd s
tl (xfilter (pres x) s) = filter x (tl s)
xfilter (drop u) s = xfilter u (tl s)

filter-comp : ∀{A} → ∀ x y (s : Stream A) →
              filter (comp x y) s ~ filter x (filter y s)
xfilter-comp : ∀{A} → ∀ u v (s : Stream A) →
               xfilter (xcomp u v) s ~ xfilter u (xfilter v s)

filter-comp x y s = xfilter-comp (out x) (out y) s

hd~(xfilter-comp (pres x') (pres y') s) = refl
tl~(xfilter-comp (pres x') (pres y') s) = filter-comp x' y' (tl s)
xfilter-comp (drop u') (pres y') s = xfilter-comp u' (out y') (tl s)
xfilter-comp (pres x') (drop v') s = xfilter-comp (pres x') v' (tl s)
xfilter-comp (drop u') (drop v') s = xfilter-comp (drop u') v' (tl s)

_≤[_]_ : ∀{A} → Stream A → W → Stream A → Set
s ≤[ x ] t = s ~ filter x t

_≤μ[_]_ : ∀{A} → Stream A → Wμ → Stream A → Set
s ≤μ[ x ] t = s ~ xfilter x t


mutual
  record _≤_ {A : Set} (s t : Stream A) : Set where
    coinductive
    field out≤ : s ≤μ t

  data _≤μ_ {A : Set} (s t : Stream A) : Set where
    ma : hd s ≡ hd t → (tl s) ≤ (tl t) → s ≤μ t
    sk : s ≤μ (tl t) → s ≤μ t

open _≤_ public

witness : ∀{A} {s t : Stream A} → s ≤ t → W
xwitness : ∀{A} {s t : Stream A} → s ≤μ t → Wμ

out (witness p) = xwitness (out≤ p)

xwitness (ma _ t≤) = pres (witness t≤)
xwitness (sk u)    = drop (xwitness u)

impl₁ : ∀{A} {s t : Stream A} → (p : s ≤ t) → s ≤[ witness p ] t
ximpl₁ : ∀{A} {s t : Stream A} → (p : s ≤μ t) → s ≤μ[ xwitness p ] t

impl₁ {A} {s} {t} p = ximpl₁ (out≤ p)

hd~ (ximpl₁ (ma h≡ t≤)) = h≡
tl~ (ximpl₁ (ma h≡ t≤)) = impl₁ t≤
ximpl₁ (sk q) = ximpl₁ q

impl₂ : ∀{A} {s t : Stream A} (x : W) → s ≤[ x ] t → s ≤ t
ximpl₂ : ∀{A} {s t : Stream A} (u : Wμ) → s ≤μ[ u ] t → s ≤μ t

out≤ (impl₂ x p) = ximpl₂ (out x) p

ximpl₂ (pres x) p = ma (hd~ p) (impl₂ x (tl~ p))
ximpl₂ (drop u) p = sk (ximpl₂ u p)

≤⇔filter-≤ : ∀{A} (s t : Stream A) →
             s ≤ t ⇔ ∃ λ p → s ≤[ p ] t
≤⇔filter-≤ s t = equivalence (λ x → witness x , impl₁ x)
                             (λ {(x , p) → impl₂ x p})

filter-resp~ : ∀{A} {s t : Stream A} (x : W) →
               s ~ t → filter x s ~ filter x t
xfilter-resp~ : ∀{A} {s t : Stream A} (u : Wμ) →
                s ~ t → xfilter u s ~ xfilter u t

filter-resp~ x p = xfilter-resp~ (out x) p
hd~ (xfilter-resp~ (pres x) p) = hd~ p
tl~ (xfilter-resp~ (pres x) p) = filter-resp~ x (tl~ p)
xfilter-resp~ (drop u) p = xfilter-resp~ u (tl~ p)


{-
We prove transitivity of the witnessed substream relation by
r ~ filter x s
  ~ filter x (filter y t)
  ~ filter (comp x y) t

-}
≤-filter-trans : ∀{A} {r s t : Stream A} {x y} →
                 r ≤[ x ] s → s ≤[ y ] t → r ≤[ comp x y ] t
≤-filter-trans {x = x} {y} p q =
  ~trans p (
    ~trans (filter-resp~ x q)
           (~sym (filter-comp x y _)))

≤-trans : ∀{A} {r s t : Stream A} →
          r ≤ s → s ≤ t → r ≤ t
≤-trans p q =
  impl₂ (comp (witness p) (witness q))
        (≤-filter-trans {x = (witness p)} {y = (witness q)}
                        (impl₁ p) (impl₁ q))
