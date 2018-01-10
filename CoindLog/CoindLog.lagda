\begin{code}
{-# OPTIONS --without-K #-}
\end{code}

\begin{code}
module CoindLog where

open import Data.List as List
open import Data.Nat hiding (pred)
open import Data.Nat.Properties
open import Data.Unit hiding (_≤_)
open import Data.Product as Prod
open import Function
\end{code}

In the following, we define relations of arbitrary arity.
These subsume sets (0-ary relations) and predicates (1-ary relations).
\begin{code}
Arity : Set₁
Arity = List Set

Rel : Arity → Set₁
Rel []        = Set
Rel (X ∷ Xs)  = X → Rel Xs

_⊆_ : {ar : Arity} → Rel ar → Rel ar → Set
_⊆_ {[]}      R S = R → S
_⊆_ {X ∷ ar}  R S = ∀ (x : X) → R x ⊆ S x

⊆-refl : {ar : Arity} (R : Rel ar) → R ⊆ R
⊆-refl {[]}      R = id
⊆-refl {X ∷ ar}  R = λ x → ⊆-refl (R x)

⊆-trans : {ar : Arity} {R S T : Rel ar} → R ⊆ S → S ⊆ T → R ⊆ T
⊆-trans {[]}      p q = q ∘ p
⊆-trans {X ∷ ar}  p q = λ x → ⊆-trans {ar} (p x) (q x)

_⋀_ : {ar : Arity} → Rel ar → Rel ar → Rel ar
_⋀_ {[]} R S = R × S
_⋀_ {X ∷ ar} R S = λ x → R x ⋀ S x

⋀-mono : ∀ {ar : Arity} {R S R' S' : Rel ar} →
         R ⊆ R' → S ⊆ S' → (R ⋀ S) ⊆ (R' ⋀ S')
⋀-mono {[]}      p q = Prod.map p q
⋀-mono {X ∷ ar}  p q = λ x → ⋀-mono {ar} (p x) (q x)

⋀-pair : ∀ {ar : Arity} {R₁ R₂ S : Rel ar} →
         S ⊆ R₁ → S ⊆ R₂ → S ⊆ (R₁ ⋀ R₂)
⋀-pair {[]}      p q = < p , q >
⋀-pair {X ∷ ar}  p q = λ x → ⋀-pair {ar} (p x) (q x)

\end{code}

Full relation
\begin{code}
Top : {ar : Arity} → Rel ar
Top {[]}        = ⊤
Top {X ∷ ar} x  = Top {ar}

Top! : {ar : Arity} → (R : Rel ar) → R ⊆ Top
Top! {[]}      R = λ x → tt
Top! {X ∷ ar}  R = λ x → Top! (R x)
\end{code}

Next, we introduce relation transformer, which are monotone functions on
the lattice of relations.
\begin{code}
RelT₀ : (ar : Arity) → Set₁
RelT₀ ar = Rel ar → Rel ar

Monotone : {ar : Arity} → RelT₀ ar → Set₁
Monotone Φ = ∀ R S → R ⊆ S → Φ R ⊆ Φ S

record RelT (ar : Arity) : Set₁ where
  constructor relT
  field
    trans  : RelT₀ ar
    mono   : Monotone trans

_⊑_ : {ar : Arity} → RelT ar → RelT ar → Set₁
(relT F _) ⊑ (relT G _) = ∀ R → F R ⊆ G R

_⊚_ : {ar : Arity} → RelT ar → RelT ar → RelT ar
(relT G monoG) ⊚ (relT F monoF) = relT (G ∘ F) mono
  where
    mono : (R S : Rel _) → R ⊆ S → G (F R) ⊆ G (F S)
    mono R S p = monoG (F R) (F S) (monoF R S p)

_⊗₀_ : {ar : Arity} → RelT₀ ar → RelT₀ ar → RelT₀ ar
(F ⊗₀ G) R = F R ⋀ G R

_⊗_ : {ar : Arity} → RelT ar → RelT ar → RelT ar
_⊗_ {ar} (relT F monoF) (relT G monoG) = relT (F ⊗₀ G) mono
  where
    mono : Monotone (F ⊗₀ G)
    mono R S R⊆S = ⋀-mono {ar} (monoF R S R⊆S) (monoG R S R⊆S)

pairT : ∀{ar} {T₁ T₂ U : RelT ar} → U ⊑ T₁ → U ⊑ T₂ → U ⊑ (T₁ ⊗ T₂)
pairT {ar} p q R = ⋀-pair {ar} (p R) (q R)
\end{code}

Compatible up-to techniques
\begin{code}
record CompatUpTo {ar : Arity} (Φ : RelT ar) : Set₁ where
  constructor compatUpTo
  field
    tech    : RelT ar
    compat  : (tech ⊚ Φ) ⊑ (Φ ⊚ tech)
  open RelT tech public
\end{code}

Terms are elements that can occur in relations
\begin{code}
Terms : Arity → Set
Terms [] = ⊤
Terms (X ∷ Xs) = X × Terms Xs

_∈'_ : {ar : Arity} → Terms ar → Rel ar → Set
_∈'_ {[]}     ts        R = R
_∈'_ {X ∷ ar} (t , ts)  R = ts ∈' R t

∈-mono : {ar : Arity} {R S : Rel ar} → R ⊆ S → ∀ ts → ts ∈' R → ts ∈' S
∈-mono {[]}      p ts        q = p q
∈-mono {x ∷ ar}  p (t , ts)  q = ∈-mono (p t) ts q

∈-⋀-distr : {ar : Arity} {R S : Rel ar} →
            ∀ ts → ts ∈' R × ts ∈' S → ts ∈' (R ⋀ S)
∈-⋀-distr {[]}      ts        p       = p
∈-⋀-distr {X ∷ ar}  (t , ts)  (p , q) = ∈-⋀-distr {ar} ts (p , q)

Top-∈ : {ar : Arity} → (ts : Terms ar) → ts ∈' Top
Top-∈ {[]}     _         = tt
Top-∈ {x ∷ ar} (t , ts)  = Top-∈ ts
\end{code}

Indexed relations
\begin{code}
IRel₀ : Arity → Set₁
IRel₀ ar = ℕ → Rel ar

record IRel (ar : Arity) : Set₁ where
  constructor iRel
  field
    rel  : IRel₀ ar
    dec  : ∀ {n m} → m ≤ n → rel n ⊆ rel m

_≼_ : {ar : Arity} → IRel ar → IRel ar → Set
(iRel R _) ≼ (iRel S _) = ∀ n → R n ⊆ S n

≼-refl : {ar : Arity} (R : IRel ar) → R ≼ R
≼-refl (iRel R _) n = ⊆-refl (R n)

LiftT : {ar : Arity} → RelT ar → IRel ar → IRel ar
LiftT {ar} (relT Φ mono) (iRel R decR) = iRel ΦR dec
  where
    ΦR : IRel₀ ar
    ΦR n = Φ (R n)

    dec : {n m : ℕ} → m ≤ n → ΦR n ⊆ ΦR m
    dec {n} {m} p = mono (R n) (R m) (decR p)

liftT-mono : ∀ {ar : Arity} (F : RelT ar) {R S} →
             R ≼ S → LiftT F R ≼ LiftT F S
liftT-mono (relT Φ mono) p n = mono _ _ (p n)

\end{code}

Indexed formulas
\begin{code}
IForm₀ : Set₁
IForm₀ = ℕ → Set

IForm : Set₁
IForm = IRel []

-- | Rexport destructors of IRel with more fitting names
module IForm (φ : IForm) where
  open IRel φ public renaming (rel to form)

pattern iForm φ dec = iRel φ dec
\end{code}

Some useful constructions form indexed formulas
\begin{code}
infix 4 _∈_ _∈₀_

_∈₀_ : {ar : Arity} → Terms ar → IRel₀ ar → IForm₀
(ts ∈₀ R) n = ts ∈' R n

_∈_ : {ar : Arity} → Terms ar → IRel ar → IForm
ts ∈ (iRel R decR) = iForm (ts ∈₀ R) dec
  where
    dec : {n m : ℕ} → m ≤ n → ts ∈' R n → ts ∈' R m
    dec m≤n p = ∈-mono (decR m≤n) ts p

_⇒₀_ : IForm₀ → IForm₀ → IForm₀
(φ ⇒₀ ψ) n = ∀ m → m ≤ n → φ m → ψ m

infix 3 _⇒_

_⇒_ : IForm → IForm → IForm
(iForm φ decφ) ⇒ (iForm ψ decψ) = iForm (φ ⇒₀ ψ) dec
  where
    dec : {n m : ℕ} → m ≤ n → (φ ⇒₀ ψ) n → (φ ⇒₀ ψ) m
    dec m≤n p k k≤m q = decψ ≤-refl (p k (≤-trans k≤m m≤n) q)

_∧₀_ : IForm₀ → IForm₀ → IForm₀
(φ ∧₀ ψ) n = φ n × ψ n

_∧_ : IForm → IForm → IForm
(iForm φ decφ) ∧ (iForm ψ decψ) = iForm (φ ∧₀ ψ) dec
  where
    dec : {n m : ℕ} → m ≤ n → (φ ∧₀ ψ) n → (φ ∧₀ ψ) m
    dec m≤n (p , q) = (decφ m≤n p , decψ m≤n q)

infix 2 _⟶_

_⟶_ : IForm → IForm → Set
_⟶_ = _≼_

iId : ∀ φ → φ ⟶ φ
iId = ≼-refl

≼→∈ : {ar : Arity} {R S : IRel ar} → R ≼ S → ∀ ts → ts ∈ R ⟶ ts ∈ S
≼→∈ p ts n q = ∈-mono (p n) ts q

i⊤ : IForm
i⊤ = iForm (λ _ → ⊤) (λ _ x → x)

i⊤-final : ∀ φ → (φ ⟶ i⊤)
i⊤-final φ n _ = tt

i⊤-intro : ∀ {φ} → φ ⟶ i⊤ ∧ φ
i⊤-intro n p = tt , p

infixr 9 _⊛_

_⊛_ : ∀ {P Q S} → (g : Q ⟶ S) (f : P ⟶ Q) → P ⟶ S
(g ⊛ f) n x = g n (f n x)

abstr : ∀ {φ ψ γ} → (φ ∧ ψ ⟶ γ) → (φ ⟶ ψ ⇒ γ)
abstr {iForm φ decφ} p n φn m m≤n ψm = p m (decφ m≤n φn , ψm)

unabstr : ∀ {φ ψ γ} → (φ ⟶ ψ ⇒ γ) → (φ ∧ ψ ⟶ γ)
unabstr p n φ∧ψn =
  let φn = proj₁ φ∧ψn
      ψn = proj₂ φ∧ψn
  in p n φn n ≤-refl ψn

ev : ∀ φ ψ → (φ ⇒ ψ) ∧ φ ⟶ ψ
ev φ ψ = unabstr {φ ⇒ ψ} {φ} {ψ} (iId (φ ⇒ ψ))

π₁ : ∀ {φ ψ} → φ ∧ ψ ⟶ φ
π₁ n = proj₁

π₂ : ∀ {φ ψ} → φ ∧ ψ ⟶ ψ
π₂ n = proj₂

pair : ∀ {φ ψ γ} → (γ ⟶ φ) → (γ ⟶ ψ) → (γ ⟶ φ ∧ ψ)
pair f g n p = (f n p , g n p)

map-∧ : ∀ {φ ψ φ' ψ'} → (φ ⟶ φ') → (ψ ⟶ ψ') → (φ ∧ ψ ⟶ φ' ∧ ψ')
map-∧ {φ} {ψ} {φ'} {ψ'} f g =
  pair {φ'} {ψ'} {φ ∧ ψ}
    (_⊛_ {φ ∧ ψ} {φ} {φ'} f (π₁ {φ} {ψ}))
    (_⊛_ {φ ∧ ψ} {ψ} {ψ'} g (π₂ {φ} {ψ}))

∈-liftT-⊗-distr : ∀ {ar} (T₁ T₂ : RelT ar) → ∀ P s →
                  ((s ∈ LiftT T₁ P) ∧ (s ∈ LiftT T₂ P)) ⟶
                  (s ∈ LiftT (T₁ ⊗ T₂) P)
∈-liftT-⊗-distr {ar} T₁ T₂ P s n x =
  let p₁ = π₁ {s ∈ LiftT T₁ P} {s ∈ LiftT T₂ P}
      p₂ = π₂ {s ∈ LiftT T₁ P} {s ∈ LiftT T₂ P}
  in ∈-⋀-distr s (p₁ n x , p₂ n x)
\end{code}

Later modality for indexed relations
\begin{code}
▶ : {ar : Arity} → IRel ar → IRel ar
▶ {ar} (iRel R decR) = iRel ▶R dec
  where
    ▶R : IRel₀ ar
    ▶R zero     = Top
    ▶R (suc n)  = R n

    dec : {n m : ℕ} → m ≤ n → ▶R n ⊆ ▶R m
    dec {n}         {.0}        z≤n        = Top! (▶R n)
    dec {.(suc _)}  {.(suc _)}  (s≤s m≤n)  = decR m≤n

next : (φ : IForm) → φ ⟶ ▶ φ
next _               zero     p = tt
next (iForm φ decφ)  (suc n)  p = decφ {1 + n} (n≤1+n n) p

mon : {φ ψ : IForm} → (φ ⟶ ψ) → (▶ φ ⟶ ▶ ψ)
mon p zero     q = tt
mon p (suc n)  q = p n q

▶-∧-distr : (φ ψ : IForm) → ▶ (φ ∧ ψ) ⟶ (▶ φ ∧ ▶ ψ)
▶-∧-distr φ ψ = pair {▶ φ} {▶ ψ} {▶ (φ ∧ ψ)}
                    (mon {φ ∧ ψ} {φ} (π₁ {φ} {ψ}))
                    (mon {φ ∧ ψ} {ψ} (π₂ {φ} {ψ}))

▶-pres-∧ : (φ ψ : IForm) → (▶ φ ∧ ▶ ψ) ⟶ ▶ (φ ∧ ψ)
▶-pres-∧ _ _ zero     p = tt
▶-pres-∧ _ _ (suc n)  p = p

\end{code}

Löb induction
\begin{code}
löb : {φ : IForm} → (▶ φ ⇒ φ) ⟶ φ
löb      zero     p = p zero z≤n tt
löb {φ}  (suc n)  p =
  p (suc n) ≤-refl (löb {φ} n (λ m m≤n ▶φm → p m (≤-step m≤n) ▶φm))

meta-löb : {φ : IForm} →
  (▶ φ ⟶ φ)
  → -----------------------
  (i⊤ ⟶ φ)
meta-löb {φ} f =
  _⊛_ {_} {▶ φ ⇒ φ} {φ}
  (löb {φ})
  (abstr {i⊤} {▶ φ} {φ}
    (_⊛_ {i⊤ ∧ ▶ φ} {▶ φ} {φ}
      f
      (π₂ {i⊤} {▶ φ})))

pack : List IForm → IForm
pack []        = i⊤
pack (φ ∷ φs)  = (pack φs) ∧ φ

infixl 1 _⊢_ ⊢_

_⊢_ : List IForm → IForm → Set
φs ⊢ ψ = pack φs ⟶ ψ

⊢_ : IForm → Set
⊢ φ = [] ⊢ φ
-- ⊢ φ = ∀ n → IForm.form φ n

valid : ∀{φ} → ⊢ φ → ∀ n → IForm.form φ n
valid p n = p n tt

meta-i⊤ : ∀{φ} → (i⊤ ⟶ φ) → ⊢ φ
meta-i⊤ = id

meta-i⊤₁ : ∀{φ} → ⊢ φ → (i⊤ ⟶ φ)
meta-i⊤₁ = id

meta-axiom : ∀{φ} → (i⊤ ⟶ φ) → ∀ ψ → (ψ ⟶ φ)
meta-axiom {φ} f ψ = _⊛_ {ψ} {i⊤} {φ} f (i⊤-final ψ)

-- meta-löb' : {φ : IForm} →
--   ⊢ (▶ φ ⇒ φ)
--   → -----------------------
--   ⊢ φ
-- meta-löb' {φ} p =
--   meta-i⊤ {φ}
--     (_⊛_ {_} {▶ φ ⇒ φ} {φ}
--       (löb {φ})
--       (meta-i⊤₁ {▶ φ ⇒ φ} p))

-- cut' : {φ ψ γ : IForm} →
--   ⊢ φ ⇒ ψ →
--   ⊢ ψ ⇒ γ
--   → -----------------------
--   ⊢ φ ⇒ γ
-- cut' {φ} {ψ} {γ} p q =
--   let f = unabstr {i⊤} {φ} {ψ} (meta-i⊤₁ {φ ⇒ ψ} p)
--       g = unabstr {i⊤} {ψ} {γ} (meta-i⊤₁ {ψ ⇒ γ} q)
--       g' = _⊛_ {ψ} {i⊤ ∧ ψ} {γ} g (pair {i⊤} {ψ} {ψ} (i⊤-final ψ) (iId ψ))
--       h = abstr {i⊤} {φ} {γ} (_⊛_ {i⊤ ∧ φ} {ψ} {γ} g' f)
--   in meta-i⊤ {φ ⇒ γ} h

-- axiom : {Γ : List IForm} {φ ψ : IForm} →
--   φ ⟶ ψ →
--   -----------
--   φ ∷ Γ ⊢ ψ
-- axiom {Γ} {φ} {ψ} f =
--     _⊛_ {pack Γ ∧ φ} {φ} {ψ}
--     f
--     (π₂ {pack Γ} {φ})

axiom : {Γ : List IForm} {φ ψ : IForm} →
  φ ⟶ ψ →
  -----------
  Γ ⊢ φ ⇒ ψ
axiom {Γ} {φ} {ψ} f =
  abstr {pack Γ} {φ} {ψ}
    (_⊛_ {pack Γ ∧ φ} {φ} {ψ}
      f
      (π₂ {pack Γ} {φ}))

cut : {Γ : List IForm} {φ ψ : IForm} →
  Γ ⊢ φ →
  (φ ∷ Γ) ⊢ ψ
  → -----------------------
  Γ ⊢ ψ
cut {Γ} {φ} {ψ} p q =
  let p' = pair {pack Γ} {φ} {pack Γ} (iId (pack Γ)) p
  in _⊛_ {pack Γ} {pack Γ ∧ φ} {ψ} q p'

-- cut' : ∀ {Γ} {φ ψ γ : IForm} →
--   Γ ⊢ φ ⇒ ψ →
--   Γ ⊢ ψ ⇒ γ
--   → -----------------------
--   Γ ⊢ φ ⇒ γ
-- cut' {Γ} {φ} {ψ} {γ} p q = {!!}

proj : (Γ : List IForm) (φ : IForm) →
  -----------------------
  φ ∷ Γ ⊢ φ
proj Γ φ = π₂ {pack Γ} {φ}

weaken : {Γ : List IForm} {φ : IForm} (ψ : IForm) →
  Γ ⊢ φ                   →
  -----------------------
  ψ ∷ Γ ⊢ φ
weaken {Γ} {φ} ψ p =
  _⊛_ {pack Γ ∧ ψ} {pack Γ} {φ} p (π₁ {pack Γ} {ψ})

⇒-intro : {Γ : List IForm} {φ ψ : IForm} →
  (φ ∷ Γ) ⊢ ψ
  → -----------------------
  Γ ⊢ φ ⇒ ψ
⇒-intro {Γ} {φ} {ψ} p = abstr {pack Γ} {φ} {ψ} p

⇒-elim : {Γ : List IForm} {φ ψ : IForm} →
  Γ ⊢ φ ⇒ ψ              →
  Γ ⊢ φ                  →
  -----------------------
  Γ ⊢ ψ
⇒-elim {Γ} {φ} {ψ} p q =
  _⊛_ {pack Γ} {(φ ⇒ ψ) ∧ φ} {ψ}
  (ev φ ψ)
  (pair {φ ⇒ ψ} {φ} {pack Γ} p q)

∧-intro : {Γ : List IForm} {φ ψ : IForm} →
  Γ ⊢ φ                   →
  Γ ⊢ ψ                   →
  -----------------------
  Γ ⊢ φ ∧ ψ
∧-intro {Γ} {φ} {ψ} p q = pair {φ} {ψ} {pack Γ} p q

löb' : {Γ : List IForm} {φ : IForm} →
  (▶ φ ∷ Γ) ⊢ φ
  → -----------------------
  Γ ⊢ φ
löb' {Γ} {φ} p =
  _⊛_ {pack Γ} {▶ φ ⇒ φ} {φ}
  (löb {φ})
  (abstr {pack Γ} {▶ φ} {φ} p)

mon' : ∀ {Γ} {φ ψ : IForm} →
  Γ ⊢ ▶ (φ ⇒ ψ) →
  ----------------
  Γ ⊢ ▶ φ ⇒ ▶ ψ
mon' {Γ} {φ} {ψ} p =
  let p' = _⊛_ {pack Γ ∧ ▶ φ} {▶ (φ ⇒ ψ) ∧ ▶ φ} {▶ ψ}
               (_⊛_ {▶ (φ ⇒ ψ) ∧ ▶ φ} {▶ ((φ ⇒ ψ) ∧ φ)} {▶ ψ}
                 (mon {(φ ⇒ ψ) ∧ φ} {ψ} (ev φ ψ))
                 (▶-pres-∧ (φ ⇒ ψ) φ))
               (map-∧ {pack Γ} {▶ φ} {▶ (φ ⇒ ψ)} {▶ φ} p (iId (▶ φ)))
  in abstr {pack Γ} {▶ φ} {▶ ψ} p'

next' : ∀ {Γ} {φ : IForm} →
  Γ ⊢ φ →
  ----------------
  Γ ⊢ ▶ φ
next' {Γ} {φ} p = _⊛_ {pack Γ} {φ} {▶ φ} (next φ) p

▶-∧-distr' : ∀ {Γ} {φ ψ : IForm} →
  Γ ⊢ ▶ (φ ∧ ψ) →
  ----------------
  Γ ⊢ ▶ φ ∧ ▶ ψ
▶-∧-distr' {Γ} {φ} {ψ} p =
  _⊛_ {pack Γ} {▶ (φ ∧ ψ)} {▶ φ ∧ ▶ ψ} (▶-∧-distr φ ψ) p

▶-pres-∧' : ∀ {Γ} {φ ψ : IForm} →
  Γ ⊢ ▶ φ ∧ ▶ ψ →
  ----------------
  Γ ⊢ ▶ (φ ∧ ψ)
▶-pres-∧' {Γ} {φ} {ψ} p =
  _⊛_ {pack Γ} {▶ φ ∧ ▶ ψ} {▶ (φ ∧ ψ)} (▶-pres-∧ φ ψ) p


-- ▶' : List IForm → List IForm
-- ▶' = List.map ▶

-- ▶-pres-∧' : (Γ : List IForm) → pack (▶' Γ) ⟶ ▶ (pack Γ)
-- ▶-pres-∧' [] = next i⊤
-- ▶-pres-∧' (φ ∷ Γ) =
--   _⊛_ {pack (▶' Γ) ∧ ▶ φ} {▶ (pack Γ) ∧ ▶ φ} {▶ (pack Γ ∧ φ)}
--     (▶-pres-∧ (pack Γ) φ)
--     (map-∧ {pack (▶' Γ)} {▶ φ} {▶ (pack Γ)} {▶ φ}
--       (▶-pres-∧' Γ)
--       (iId (▶ φ)))

-- mon'' : ∀ {Γ} {φ : IForm} →
--   Γ ⊢ φ →
--   ----------------
--   ▶' Γ ⊢ ▶ φ
-- mon'' {Γ} {φ} p =
--   _⊛_ {pack (▶' Γ)} {▶ (pack Γ)} {▶ φ}
--     (mon {pack Γ} {φ} p)
--     (▶-pres-∧' Γ)

∈-liftT-⊗-distr' : ∀ {Γ} {ar} (T₁ T₂ : RelT ar) →
  ∀ P s →
  -----------------------------------------------------
  Γ ⊢ ((s ∈ LiftT T₁ P) ∧ (s ∈ LiftT T₂ P)) ⇒ (s ∈ LiftT (T₁ ⊗ T₂) P)
∈-liftT-⊗-distr' {Γ} T₁ T₂ P s =
  axiom {Γ} {(s ∈ LiftT T₁ P) ∧ (s ∈ LiftT T₂ P)} {s ∈ LiftT (T₁ ⊗ T₂) P}
    (∈-liftT-⊗-distr T₁ T₂ P s)

-- ∈-liftT-⊗-distr' : ∀ {Γ} {ar} (T₁ T₂ : RelT ar) → ∀ P s →
--   Γ ⊢ ((s ∈ LiftT T₁ P) ∧ (s ∈ LiftT T₂ P)) →
--   -----------------------------------------------------
--   Γ ⊢ (s ∈ LiftT (T₁ ⊗ T₂) P)
-- ∈-liftT-⊗-distr' {Γ} T₁ T₂ P s p =
--   _⊛_ {pack Γ} {(s ∈ LiftT T₁ P) ∧ (s ∈ LiftT T₂ P)} {s ∈ LiftT (T₁ ⊗ T₂) P}
--     (∈-liftT-⊗-distr T₁ T₂ P s)
--     p
\end{code}

\begin{code}
module ChainReasoning {ar : Arity} (T : RelT ar) where
  open RelT T renaming (trans to Φ; mono to monoΦ)

  \end{code}

  Final chain for a monotone operator and the associated
  \begin{code}
  Seq₀ : IRel₀ ar
  Seq₀ zero     = Top
  Seq₀ (suc n)  = Φ (Seq₀ n)

  Seq : IRel ar
  Seq = iRel Seq₀ dec
    where
      dec : {n m : ℕ} → m ≤ n → Seq₀ n ⊆ Seq₀ m
      dec {n}      {.0}        z≤n   = Top! (Seq₀ n)
      dec {suc n}  {suc m}  (s≤s p)  = monoΦ (Seq₀ n) (Seq₀ m) (dec p)
\end{code}

Unfolding of the operator on the sequence.
This will allow us to do recursion steps with the Löb rule.
\begin{code}
  seq : (ts : Terms ar) → ▶ (ts ∈ LiftT T Seq) ⟶ (ts ∈ Seq)
  seq ts zero     p = Top-∈ ts
  seq ts (suc n)  p = p

  seq' : {Γ : List IForm} →
    (ts : Terms ar) →
    ---------------------------------
    Γ ⊢ ▶ (ts ∈ LiftT T Seq) ⇒ ts ∈ Seq
  seq' {Γ} ts = axiom {Γ} {▶ (ts ∈ LiftT T Seq)} {ts ∈ Seq} (seq ts)

\end{code}

Compatible up-to techniques give us inclusions on every step of the
sequence.
This will allow us to import them into recursive proofs.
\begin{code}
  compat-seq : (F : CompatUpTo T) → (LiftT (CompatUpTo.tech F) Seq) ≼ Seq
  compat-seq F zero     = Top! (CompatUpTo.trans F Top)
  compat-seq F (suc n)  =
    ⊆-trans {ar}
            (compat (Seq₀ n))
            (monoΦ (LiftT tech Seq .IRel.rel n) (Seq₀ n) (compat-seq F n))
    where
      open CompatUpTo F renaming (trans to Ψ)

  compat-∈ : (F : CompatUpTo T) (ts : Terms ar) →
             (ts ∈ LiftT (CompatUpTo.tech F) Seq) ⟶ (ts ∈ Seq)
  compat-∈ F =
    ≼→∈ {ar} {LiftT (CompatUpTo.tech F) Seq} {Seq} (compat-seq F)

  compat-step : (F : CompatUpTo T) →
                (LiftT (CompatUpTo.tech F) (▶ Seq)) ≼ (▶ Seq)
  compat-step F zero     = Top! (CompatUpTo.trans F Top)
  compat-step F (suc n)  = compat-seq F n

  compat-∈-step : (F : CompatUpTo T) (ts : Terms ar) →
                  ▶ (ts ∈ LiftT (CompatUpTo.tech F) Seq) ⟶ ▶ (ts ∈ Seq)
  compat-∈-step F ts =
    mon {ts ∈ LiftT (CompatUpTo.tech F) Seq} {ts ∈ Seq} (compat-∈ F ts)

  compat-∈-step' : {Γ : List IForm} →
    (F : CompatUpTo T)
    (ts : Terms ar) →
    -------------------
    Γ ⊢ ▶ (ts ∈ LiftT (CompatUpTo.tech F) Seq) ⇒ ▶ (ts ∈ Seq)
  compat-∈-step' {Γ} F ts =
    axiom {Γ} {▶ (ts ∈ LiftT (CompatUpTo.tech F) Seq)} {▶ (ts ∈ Seq)}
    (compat-∈-step F ts)
\end{code}

TODO:
* Extend up-to techniques to transformations of arbitrary arity;
  this is needed, for instance, for transitivity
* Example 1: Bisimilarity for streams + proof that ⊕ is commutative
* Example 2: Selection is homomorphism
* Example 3: Observational equivalence (do we need indexed relations?)
