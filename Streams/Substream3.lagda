\begin{code}
-- | In this module we show that the substream relation is transitive.
module Substream3 (A : Set) where

open import Stream
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
open import Data.Product
open import Function.Equivalence

open Bisim (P.setoid A)
import Relation.Binary.EqReasoning as EqR
open EqR (P.setoid A) public hiding (_≡⟨_⟩_)
open ~-Reasoning renaming (begin_ to begin~_; _∎ to _∎~)

mutual
  record F : Set where
    coinductive
    field out : Fμ

  data Fμ : Set where
    pres : F → Fμ
    drop : Fμ → Fμ

open F public

μfilter : Fμ → Stream A → Stream A
filter  : F  → Stream A → Stream A

filter x = μfilter (out x)

μfilter (pres x) s .hd = s .hd
μfilter (pres x) s .tl = filter x (s .tl)
μfilter (drop u) s     = μfilter u (s .tl)

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

filter-comp : ∀ x y (s : Stream A) →
              filter (y • x) s ~ filter y (filter x s)
μfilter-comp : ∀ u v (s : Stream A) →
               μfilter (v •μ u) s ~ μfilter v (μfilter u s)

filter-comp x y s = μfilter-comp (out x) (out y) s

hd≈(μfilter-comp (pres x) (pres y) s) = refl
tl~(μfilter-comp (pres x) (pres y) s) = filter-comp x y (tl s)
μfilter-comp (pres x) (drop v) s = μfilter-comp (out x) v (tl s)
\end{code}
The following cases are just the same, they need to be
there for Agda to reduce the definition of μcomp
\begin{code}
μfilter-comp (drop u) (pres x) s = μfilter-comp u (pres x) (tl s)
μfilter-comp (drop u) (drop v) s = μfilter-comp u (drop v) (tl s)

_≤[_]_ : Stream A → F → Stream A → Set
s ≤[ x ] t = s ~ filter x t

_≤μ[_]_ : Stream A → Fμ → Stream A → Set
s ≤μ[ x ] t = s ~ μfilter x t


mutual
  record _≤_ (s t : Stream A) : Set where
    coinductive
    field out≤ : s ≤μ t

  data _≤μ_ (s t : Stream A) : Set where
    ma : hd s ≡ hd t → (tl s) ≤ (tl t) → s ≤μ t
    sk : s ≤μ (tl t) → s ≤μ t

open _≤_ public

witness : {s t : Stream A} → s ≤ t → F
μwitness : ∀ {s t : Stream A} → s ≤μ t → Fμ

out (witness p) = μwitness (out≤ p)

μwitness (ma _ t≤) = pres (witness t≤)
μwitness (sk u)    = drop (μwitness u)

≤⇒filter≤ : ∀{s t : Stream A} → (p : s ≤ t) → s ≤[ witness p ] t
≤μ⇒μfilter≤ : ∀{s t : Stream A} → (p : s ≤μ t) → s ≤μ[ μwitness p ] t

≤⇒filter≤ {s} {t} p = ≤μ⇒μfilter≤ (out≤ p)

hd≈ (≤μ⇒μfilter≤ (ma h≡ t≤)) = h≡
tl~ (≤μ⇒μfilter≤ (ma h≡ t≤)) = ≤⇒filter≤ t≤
≤μ⇒μfilter≤ (sk q) = ≤μ⇒μfilter≤ q

filter≤⇒≤ : ∀{s t : Stream A} (x : F) → s ≤[ x ] t → s ≤ t
μfilter≤⇒≤μ : ∀{s t : Stream A} (u : Fμ) → s ≤μ[ u ] t → s ≤μ t

out≤ (filter≤⇒≤ x p) = μfilter≤⇒≤μ (out x) p

μfilter≤⇒≤μ (pres x) p = ma (hd≈ p) (filter≤⇒≤ x (tl~ p))
μfilter≤⇒≤μ (drop u) p = sk (μfilter≤⇒≤μ u p)

≤⇔filter-≤ : ∀(s t : Stream A) →
             s ≤ t ⇔ ∃ λ p → s ≤[ p ] t
≤⇔filter-≤ s t = equivalence (λ x → witness x , ≤⇒filter≤ x)
                             (λ {(x , p) → filter≤⇒≤ x p})

filter-resp~ : ∀{s t : Stream A} (x : F) →
               s ~ t → filter x s ~ filter x t
μfilter-resp~ : ∀{s t : Stream A} (u : Fμ) →
                s ~ t → μfilter u s ~ μfilter u t

filter-resp~ x p = μfilter-resp~ (out x) p
hd≈ (μfilter-resp~ (pres x) p) = hd≈ p
tl~ (μfilter-resp~ (pres x) p) = filter-resp~ x (tl~ p)
μfilter-resp~ (drop u) p = μfilter-resp~ u (tl~ p)

\end{code}

We prove transitivity of the witnessed substream relation by
\begin{align*}
  r & \sim \AgdaFunction{\AgdaFunction{filter}} \> \AgdaBound{x} \> \AgdaBound{s} \\
  & \sim \AgdaFunction{filter} \> \AgdaBound{x} \>
  (\AgdaFunction{filter} \> \AgdaBound{y} \> \AgdaBound{t}) \\
  & \sim \AgdaFunction{filter} \>
  (\AgdaFunction{comp} \> \AgdaBound{x} \> \AgdaBound{y}) \> \AgdaBound{t}
\end{align*}

\begin{code}
≤-filter-trans :
  ∀{r s t : Stream A} {x y} → r ≤[ x ] s → s ≤[ y ] t → r ≤[ x • y ] t
≤-filter-trans {r} {s} {t} {x} {y} p q =
  begin~
    r
  ~⟨ p ⟩
    filter x s
  ~⟨ filter-resp~ x q ⟩
    filter x (filter y t)
  ~⟨ S.sym (filter-comp y x t) ⟩
    filter (x • y) t
  ∎~
  where
    module S = Setoid stream-setoid

≤-trans : ∀{r s t : Stream A} → r ≤ s → s ≤ t → r ≤ t
≤-trans p q =
  filter≤⇒≤ (witness p • witness q)
            (≤-filter-trans {x = witness p}
                            {y = witness q}
                            (≤⇒filter≤ p)
                            (≤⇒filter≤ q)
            )

\end{code}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../7_ind-coind-tt"
%%% ispell-local-dictionary: "british"
%%% End:
