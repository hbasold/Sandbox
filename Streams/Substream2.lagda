\begin{code}
-- | In this module we show that the substream relation is transitive.
module Substream2 where
\end{code}

%<*imports>
\begin{code}
open import Data.Empty
open import Relation.Binary hiding (Rel)
open import Relation.Binary.PropositionalEquality as P
open import Data.Product
open import Function
open import Function.Equivalence hiding (_∘_; sym)
\end{code}
%</imports>

%<*streams>
\begin{code}
-- | Streams (with size annotations to ease definitions).
record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A
open Stream public

-- | Stream equality is bisimilarity
record _~_ {A : Set} (s t : Stream A) : Set where
  coinductive
  field
    hd~ : s .hd ≡ t .hd
    tl~ : s .tl ~ t .tl
open _~_ public

~refl : ∀{A} {s : Stream A} → s ~ s
hd~ ~refl = refl
tl~ ~refl = ~refl

~trans : ∀{A} {r s t : Stream A} → r ~ s → s ~ t → r ~ t
hd~ (~trans p q) = trans  (hd~ p) (hd~ q)
tl~ (~trans p q) = ~trans (tl~ p) (tl~ q)

~sym : ∀{A} {s t : Stream A} → s ~ t → t ~ s
hd~ (~sym p) = sym  (hd~ p)
tl~ (~sym p) = ~sym (tl~ p)
\end{code}
%</streams>

%<*relations>
\begin{code}
Rel : Set → Set → Set₁
Rel X Y = REL X Y _
-- Rel X Y = X → Y → Set
\end{code}
%</relations>

%<*selector-type>
\begin{code}
Pres : Set → Set → Set
Pres S _ = S

Drop : Set → Set → Set
Drop _ Sμ = Sμ

data Selμ' (S : Set) : Set where
  pres : Pres S (Selμ' S) → Selμ' S
  drop : Drop S (Selμ' S) → Selμ' S

-- | Non-dependent iteration principle for Selμ
iter-selμ : {S X : Set} → (Pres S X → X) → (Drop S X → X) → Selμ' S → X
iter-selμ p d (pres x) = p x
iter-selμ p d (drop u) = d (iter-selμ p d u)

-- | Functoriality of Selμ
Selμ₁ : {X Y : Set} → (X → Y) → Selμ' X → Selμ' Y
Selμ₁ f = iter-selμ (pres ∘ f) drop


-- PresL : Set → (Pres Set → Set


ind-selμ : {S : Set} {X : Selμ' S → Set} →
           ((s : S) → X (pres s)) →
           ((u : Selμ' S) → X u → X (drop u)) →
           (u : Selμ' S) → X u
ind-selμ p d (pres x) = p x
ind-selμ p d (drop u) = d u (ind-selμ p d u)

-- | Predicate lifting of Selμ
data Selμp {X : Set} (P : X → Set) : Selμ' X → Set where
  presp : ∀{x} → P x       → Selμp P (pres x)
  dropp : ∀{u} → Selμp P u → Selμp P (drop u)


-- | Relation lifting of Selμ
data Selμ₂ {X Y : Set} (R : Rel X Y) : Rel (Selμ' X) (Selμ' Y) where
  pres₂ : ∀{x y} → R x y       → Selμ₂ R (pres x) (pres y)
  drop₂ : ∀{u v} → Selμ₂ R u v → Selμ₂ R (drop u) (drop v)

-- | Functoriality of relation lifting of Selμ
Selμ₂₁ : {X Y : Set} → (R S : Rel X Y) → R ⇒ S → Selμ₂ R ⇒ Selμ₂ S
Selμ₂₁ R S R⇒S (pres₂ xRy) = pres₂ (R⇒S xRy)
Selμ₂₁ R S R⇒S (drop₂ p)   = drop₂ (Selμ₂₁ R S R⇒S p)

record Sel : Set where
  coinductive
  field out : Selμ' Sel

open Sel public

Selμ : Set
Selμ = Selμ' Sel
\end{code}
%</selector-type>

%<*l>
\begin{code}
\end{code}
%</l>

%<*corecursor>
\begin{code}
sel-do-rec : {X : Set} → (X → Selμ' X) → Selμ' X → Selμ
corec-sel : {X : Set} → (X → Selμ' X) → X → Sel

corec-sel {X} c x .out = sel-do-rec c (c x)
sel-do-rec c (pres x') = pres (corec-sel c x')
sel-do-rec c (drop u)  = drop (sel-do-rec c u)

\end{code}
%</corecursor>


%<*selector-bisimilarity>
\begin{code}
mutual
  record _≈_ (x y : Sel) : Set where
    coinductive
    field out≈ : (x .out) ≈μ (y .out)

  data _≈μ_ : Selμ → Selμ → Set where
    pres≈ : {x y : Sel} → x ≈ y → (pres x) ≈μ (pres y)
    drop≈ : {u v : Selμ} → u ≈μ v → (drop u) ≈μ (drop v)

open _≈_ public

Sel-Bisim : (Rel Sel Sel) → Set
Sel-Bisim R = ∀ s t → R s t → Selμ₂ R (s .out) (t .out)

Sel-Bisim→≈ : (R : Rel Sel Sel) → Sel-Bisim R → R ⇒ _≈_
Sel-Bisim→≈ R R-isBisim {x} {y} p .out≈ =
  do-ind (R-isBisim x y p)
  where
    do-ind : {u v : Selμ} → Selμ₂ R u v → u ≈μ v
    do-ind (pres₂ xRy) = pres≈ (Sel-Bisim→≈ R R-isBisim xRy)
    do-ind (drop₂ q)   = drop≈ (do-ind q)

≈-refl : ∀ {x} → x ≈ x
≈μ-refl : ∀ {u} → u ≈μ u
≈-refl {x} .out≈ = ≈μ-refl {x .out}
≈μ-refl {pres x'} = pres≈ ≈-refl
≈μ-refl {drop u'} = drop≈ ≈μ-refl

≈-sym : ∀ {x y} → x ≈ y → y ≈ x
≈μ-sym : ∀ {u v} → u ≈μ v → v ≈μ u
≈-sym {x} p .out≈ = ≈μ-sym {x .out} (p .out≈)
≈μ-sym (pres≈ p) = pres≈ (≈-sym p)
≈μ-sym (drop≈ p) = drop≈ (≈μ-sym p)

≈-trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
≈μ-trans : ∀ {u v w} → u ≈μ v → v ≈μ w → u ≈μ w
≈-trans {x} p q .out≈ = ≈μ-trans {x .out} (p .out≈) (q .out≈)
≈μ-trans (pres≈ p) (pres≈ q) = pres≈ (≈-trans p q)
≈μ-trans (drop≈ p) (drop≈ q) = drop≈ (≈μ-trans p q)

corec-sel-compute : {X : Set} → (c : X → Selμ' X) (x : X) →
                    corec-sel c x .out ≡ Selμ₁ (corec-sel c) (c x)
sel-do-rec-compute : {X : Set} → (c : X → Selμ' X) (u : Selμ' X) →
                     sel-do-rec c u ≡ Selμ₁ (corec-sel c) u

corec-sel-compute c x = sel-do-rec-compute c (c x)
sel-do-rec-compute c (pres x) = refl
sel-do-rec-compute c (drop u) = cong drop (sel-do-rec-compute c u)

-- Morally:
--  Sel-Bisim→≈ R R-isBisim
--    = Selμ₂₁ R _≈_ (Sel-Bisim→≈ R R-isBisim) (R-isBisim x y p)

Sel-gBisim : ∀{X Y} → (X → Selμ' X) → (Y → Selμ' Y) → (Rel X Y) → Set
Sel-gBisim c d R = ∀ x y → R x y → Selμ₂ R (c x) (d y)

_≊[_,_]_ : ∀{X Y} → X → (X → Selμ' X) → (Y → Selμ' Y) → Y → Set
x ≊[ c , d ] y = corec-sel c x ≈ corec-sel d y

Sel-gBisim→≈ : ∀ {X Y} (c : X → Selμ' X) (d : Y → Selμ' Y) (R : Rel X Y) →
               Sel-gBisim c d R → R ⇒ _≊[ c , d ]_
Sel-gBisim→≈ = {!!}

corec-sel-out≈id : ∀ x → corec-sel out x ≈ x
sel-do-rec-out≈μid : ∀ u → sel-do-rec out u ≈μ u
corec-sel-out≈id x .out≈ = sel-do-rec-out≈μid (out x)
sel-do-rec-out≈μid (pres x) = pres≈ (corec-sel-out≈id x)
sel-do-rec-out≈μid (drop u) = drop≈ (sel-do-rec-out≈μid u)

Sel-Hom : ∀{X} → (X → Selμ' X) → (X → Sel) → Set
Sel-Hom c h = ∀ x → (h x .out) ≈μ (Selμ₁ h (c x))

Graph : ∀{X} → (X → Sel) → Rel X Sel
Graph f x y = f x ≈ y

hom-graph-isBisimμ : {X : Set} → (c : X → Selμ' X) (h : X → Sel) → Sel-Hom c h →
  ∀ {u v w} → v ≈μ w → v ≈μ (Selμ₁ h u) → Selμ₂ (Graph h) u w
hom-graph-isBisimμ c h p {pres x} (pres≈ q) (pres≈ r) =
  pres₂ (≈-trans (≈-sym r) q)
hom-graph-isBisimμ c h p {drop u} (pres≈ q) ()
hom-graph-isBisimμ c h p {pres x} (drop≈ q) ()
hom-graph-isBisimμ c h p {drop u} (drop≈ q) (drop≈ r) =
  drop₂ (hom-graph-isBisimμ c h p {u} q r)

hom-graph-isBisim : {X : Set} → (c : X → Selμ' X) (h : X → Sel) → Sel-Hom c h →
                    Sel-gBisim c out (Graph h)
hom-graph-isBisim c h p x y q =
  hom-graph-isBisimμ c h p {(c x)} {(h x .out)} {(out y)} (q .out≈) (p x)

corec-sel-unique : {X : Set} → (c : X → Selμ' X) (h : X → Sel) → Sel-Hom c h →
                   ∀ x → h x ≈ corec-sel c x
corec-sel-unique c h p x = ≈-sym (lem₃ x (h x) ≈-refl)
  where
    lem₁ : Sel-gBisim c out (Graph h)
    lem₁ = hom-graph-isBisim c h p

    lem₂ : ∀ {x y} → h x ≈ y → corec-sel c x ≈ corec-sel out y
    lem₂ = Sel-gBisim→≈ c out (Graph h) lem₁

    lem₃ : ∀ x y → h x ≈ y → corec-sel c x ≈ y
    lem₃ x y p = ≈-trans (lem₂ p) (corec-sel-out≈id y)
\end{code}
%</selector-bisimilarity>


%<*selector-composition-corec>
\begin{code}


{-
The following two functions should resemble the following recursion.

comp-p x' v corresponds to, defined by iteration on v:
xcomp (pres x') (pres y') = pres (comp  x' y')
xcomp (pres x') (drop v') = drop (xcomp (pres x') v')

comp-d cu' v corresponds to, defined by iteration on v:
xcomp (drop u') (pres y') = drop (xcomp u' (out y'))
xcomp (drop u') (drop v') = drop (xcomp (drop u') v')
-}

comp-p : Sel → (Selμ → Selμ' (Sel × Sel))
comp-p x' v = iter-selμ p' d' v
  where
    p' : Sel → Selμ' (Sel × Sel)
    p' y' = pres (x' , y')

    d' : Selμ' (Sel × Sel) → Selμ' (Sel × Sel)
    d' v' = drop v'

comp-d : (Selμ → Selμ' (Sel × Sel)) → Selμ → Selμ' (Sel × Sel)
comp-d cu' v = iter-selμ p' d' v cu'
  where
    p' : Sel → (Selμ → Selμ' (Sel × Sel)) → Selμ' (Sel × Sel)
    p' y' cu' = drop (cu' (y' .out))

    d' : ((Selμ → Selμ' (Sel × Sel)) → Selμ' (Sel × Sel)) →
           (Selμ → Selμ' (Sel × Sel)) → Selμ' (Sel × Sel)
    d' C cu' = drop (C cu')

comp-coalg : Sel × Sel → Selμ' (Sel × Sel)
comp-coalg (x , y) = iter-selμ comp-p comp-d (x .out) (y .out)

comp : Sel × Sel → Sel
comp = corec-sel comp-coalg

\end{code}
%</selector-composition-corec>

%<*selector-composition>
\begin{code}
_•_ : Sel → Sel → Sel
_•μ_ : Selμ → Selμ → Selμ

(x • y) .out = (x .out) •μ (y .out)

(pres x') •μ (pres y') = pres (x' • y')
(drop u') •μ (pres y') = drop (u' •μ (y' .out))
u         •μ (drop v') = drop (u •μ v')

•≈comp : ∀ x y → (x • y) ≈ comp (x , y)
•≈comp x y = corec-sel-unique comp-coalg comp' comp'-hom (x , y)
  where
    comp' : Sel × Sel → Sel
    comp' (x , y) = x • y

    comp'-homμ : ∀ u v →
      (u •μ v) ≈μ (Selμ₁ comp' (iter-selμ comp-p comp-d u v))
    comp'-homμ (pres x') (pres y') = pres≈ ≈-refl
    comp'-homμ (pres x') (drop v') = drop≈ (comp'-homμ (pres x') v')
    comp'-homμ (drop u') (pres y') = drop≈ (comp'-homμ u' (y' .out))
    comp'-homμ (drop u') (drop v') = drop≈ (comp'-homμ (drop u') v')

    comp'-hom : Sel-Hom comp-coalg comp'
    comp'-hom (x , y) = comp'-homμ (x .out) (y .out)
\end{code}
%</selector-composition>

\begin{code}
filterμ : ∀{A} → Selμ → Stream A → Stream A

filter : ∀{A} → Sel → Stream A → Stream A
filter x = filterμ (out x)

hd (filterμ (pres x) s) = hd s
tl (filterμ (pres x) s) = filter x (tl s)
filterμ (drop u) s = filterμ u (tl s)

filter-comp : ∀{A} → ∀ x y (s : Stream A) →
              filter (x • y) s ~ filter x (filter y s)
filterμ-comp : ∀{A} → ∀ u v (s : Stream A) →
               filterμ (u •μ v) s ~ filterμ u (filterμ v s)

filter-comp x y s = filterμ-comp (out x) (out y) s

hd~(filterμ-comp (pres x') (pres y') s) = refl
tl~(filterμ-comp (pres x') (pres y') s) = filter-comp x' y' (tl s)
filterμ-comp (drop u') (pres y') s = filterμ-comp u' (out y') (tl s)
filterμ-comp (pres x') (drop v') s = filterμ-comp (pres x') v' (tl s)
filterμ-comp (drop u') (drop v') s = filterμ-comp (drop u') v' (tl s)

_≤[_]_ : ∀{A} → Stream A → Sel → Stream A → Set
s ≤[ x ] t = s ~ filter x t

_≤μ[_]_ : ∀{A} → Stream A → Selμ → Stream A → Set
s ≤μ[ x ] t = s ~ filterμ x t

{- Substream relatio without using mutual
data _≤μ'[_]_ {A : Set} (s : Stream A) (R : Stream A → Stream A → Set) (t : Stream A) : Set where
  ma : hd s ≡ hd t → R (tl s) (tl t) → s ≤μ'[ R ] t
  sk : s ≤μ'[ R ](tl t) → s ≤μ'[ R ] t

record _≤_ {A : Set} (s t : Stream A) : Set where
  coinductive
  field out≤ : s ≤μ'[ _≤_ ] t

open _≤_ public

_≤μ_ : {A : Set} → Stream A → Stream A → Set
_≤μ_ = _≤μ'[ _≤_ ]_
-}

mutual
  record _≤_ {A : Set} (s t : Stream A) : Set where
    coinductive
    field out≤ : s ≤μ t

  data _≤μ_ {A : Set} (s t : Stream A) : Set where
    ma : hd s ≡ hd t → (tl s) ≤ (tl t) → s ≤μ t
    sk : s ≤μ (tl t) → s ≤μ t

open _≤_ public

witness : ∀{A} {s t : Stream A} → s ≤ t → Sel
xwitness : ∀{A} {s t : Stream A} → s ≤μ t → Selμ

out (witness p) = xwitness (out≤ p)

xwitness (ma _ t≤) = pres (witness t≤)
xwitness (sk u)    = drop (xwitness u)

impl₁ : ∀{A} {s t : Stream A} → (p : s ≤ t) → s ≤[ witness p ] t
ximpl₁ : ∀{A} {s t : Stream A} → (p : s ≤μ t) → s ≤μ[ xwitness p ] t

impl₁ {A} {s} {t} p = ximpl₁ (out≤ p)

hd~ (ximpl₁ (ma h≡ t≤)) = h≡
tl~ (ximpl₁ (ma h≡ t≤)) = impl₁ t≤
ximpl₁ (sk q) = ximpl₁ q

impl₂ : ∀{A} {s t : Stream A} (x : Sel) → s ≤[ x ] t → s ≤ t
ximpl₂ : ∀{A} {s t : Stream A} (u : Selμ) → s ≤μ[ u ] t → s ≤μ t

out≤ (impl₂ x p) = ximpl₂ (out x) p

ximpl₂ (pres x) p = ma (hd~ p) (impl₂ x (tl~ p))
ximpl₂ (drop u) p = sk (ximpl₂ u p)

≤⇔filter-≤ : ∀{A} (s t : Stream A) →
             s ≤ t ⇔ ∃ λ p → s ≤[ p ] t
≤⇔filter-≤ s t = equivalence (λ x → witness x , impl₁ x)
                             (λ {(x , p) → impl₂ x p})

filter-resp~ : ∀{A} {s t : Stream A} (x : Sel) →
               s ~ t → filter x s ~ filter x t
filterμ-resp~ : ∀{A} {s t : Stream A} (u : Selμ) →
                s ~ t → filterμ u s ~ filterμ u t

filter-resp~ x p = filterμ-resp~ (out x) p
hd~ (filterμ-resp~ (pres x) p) = hd~ p
tl~ (filterμ-resp~ (pres x) p) = filter-resp~ x (tl~ p)
filterμ-resp~ (drop u) p = filterμ-resp~ u (tl~ p)


\end{code}

We prove transitivity of the witnessed substream relation by
\begin{align*}
  r & ∼ filter x s
    & ~ filter x (filter y t)
    & ~ filter (comp x y) t
\end{align*}

\begin{code}
≤-filter-trans : ∀{A} {r s t : Stream A} {x y} →
                 r ≤[ x ] s → s ≤[ y ] t → r ≤[ x • y ] t
≤-filter-trans {x = x} {y} p q =
  ~trans p (
    ~trans (filter-resp~ x q)
           (~sym (filter-comp x y _)))

≤-trans : ∀{A} {r s t : Stream A} →
          r ≤ s → s ≤ t → r ≤ t
≤-trans p q =
  impl₂ ((witness p) • (witness q))
        (≤-filter-trans {x = (witness p)} {y = (witness q)}
                        (impl₁ p) (impl₁ q))
\end{code}
