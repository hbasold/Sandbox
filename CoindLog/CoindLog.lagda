\begin{code}
{-# OPTIONS --without-K #-}
\end{code}

\begin{code}
module CoindLog where

open import Data.List
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

Indexed predicates
\begin{code}
IPred₀ : Set₁
IPred₀ = ℕ → Set

record IPred : Set₁ where
  constructor iPred
  field
    pred  : IPred₀
    dec   : ∀ {n m} → m ≤ n → pred n → pred m

infix 4 _∈_ _∈₀_

_∈₀_ : {ar : Arity} → Terms ar → IRel₀ ar → IPred₀
(ts ∈₀ R) n = ts ∈' R n

_∈_ : {ar : Arity} → Terms ar → IRel ar → IPred
ts ∈ (iRel R decR) = iPred (ts ∈₀ R) dec
  where
    dec : {n m : ℕ} → m ≤ n → ts ∈' R n → ts ∈' R m
    dec m≤n p = ∈-mono (decR m≤n) ts p

_⇒₀_ : IPred₀ → IPred₀ → IPred₀
(φ ⇒₀ ψ) n = ∀ m → m ≤ n → φ m → ψ m

_⇒_ : IPred → IPred → IPred
(iPred φ decφ) ⇒ (iPred ψ decψ) = iPred (φ ⇒₀ ψ) dec
  where
    dec : {n m : ℕ} → m ≤ n → (φ ⇒₀ ψ) n → (φ ⇒₀ ψ) m
    dec m≤n p k k≤m q = decψ ≤-refl (p k (≤-trans k≤m m≤n) q)

_∧₀_ : IPred₀ → IPred₀ → IPred₀
(φ ∧₀ ψ) n = φ n × ψ n

_∧_ : IPred → IPred → IPred
(iPred φ decφ) ∧ (iPred ψ decψ) = iPred (φ ∧₀ ψ) dec
  where
    dec : {n m : ℕ} → m ≤ n → (φ ∧₀ ψ) n → (φ ∧₀ ψ) m
    dec m≤n (p , q) = (decφ m≤n p , decψ m≤n q)

infix 2 _⟶_

_⟶_ : IPred → IPred → Set
(iPred φ _) ⟶ (iPred ψ _) = ∀ n → φ n → ψ n

≼→∈ : {ar : Arity} {R S : IRel ar} → R ≼ S → ∀ ts → ts ∈ R ⟶ ts ∈ S
≼→∈ p ts n q = ∈-mono (p n) ts q

i⊤ : IForm
i⊤ = iForm (λ _ → ⊤) (λ _ x → x)

i⊤-final : ∀ φ → (φ ⟶ i⊤)
i⊤-final φ n _ = tt

i⊤-intro : ∀ {φ} → φ ⟶ i⊤ ∧ φ
i⊤-intro n p = tt , p

pack : List IForm → IForm
pack []        = i⊤
pack (φ ∷ φs)  = φ ∧ (pack φs)

_⊢_ : List IForm → IForm → Set
φs ⊢ ψ = pack φs ⟶ ψ

⊢_ : IForm → Set
⊢ φ = ∀ n → IForm.form φ n

infixr 9 _⊛_

_⊛_ : ∀ {P Q S} → (g : Q ⟶ S) (f : P ⟶ Q) → P ⟶ S
(g ⊛ f) n x = g n (f n x)

abstr : ∀ {φ ψ γ} → (φ ∧ ψ ⟶ γ) → (φ ⟶ ψ ⇒ γ)
abstr {iPred φ decφ} p n φn m m≤n ψm = p m (decφ m≤n φn , ψm)

π₁ : ∀ {φ ψ} → φ ∧ ψ ⟶ φ
π₁ n = proj₁

π₂ : ∀ {φ ψ} → φ ∧ ψ ⟶ ψ
π₂ n = proj₂

pair : ∀ {φ ψ γ} → (γ ⟶ φ) → (γ ⟶ ψ) → (γ ⟶ φ ∧ ψ)
pair f g n p = (f n p , g n p)

∈-liftT-⊗-distr : ∀ {ar} (T₁ T₂ : RelT ar) → ∀ P s →
                  ((s ∈ LiftT T₁ P) ∧ (s ∈ LiftT T₂ P)) ⟶
                  (s ∈ LiftT (T₁ ⊗ T₂) P)
∈-liftT-⊗-distr {ar} T₁ T₂ P s n x =
  let p₁ = π₁ {s ∈ LiftT T₁ P} {s ∈ LiftT T₂ P}
      p₂ = π₂ {s ∈ LiftT T₁ P} {s ∈ LiftT T₂ P}
  in ∈-⋀-distr s (p₁ n x , p₂ n x)
\end{code}

Later modality for indexed predicates
\begin{code}
▶ : IPred → IPred
▶ (iPred φ decφ) = iPred ▶φ dec
  where
    ▶φ : IPred₀
    ▶φ zero     = ⊤
    ▶φ (suc n)  = φ n

    dec : {n m : ℕ} → m ≤ n → ▶φ n → ▶φ m
    dec {n}         {.0}        z≤n        p = tt
    dec {.(suc _)}  {.(suc _)}  (s≤s m≤n)  p = decφ m≤n p

next : (φ : IPred) → φ ⟶ ▶ φ
next _               zero     p = tt
next (iPred φ decφ)  (suc n)  p = decφ {1 + n} (n≤1+n n) p

mon : {φ ψ : IPred} → (φ ⟶ ψ) → (▶ φ ⟶ ▶ ψ)
mon p zero     q = tt
mon p (suc n)  q = p n q

▶-∧-distr : {φ ψ : IPred} → ▶ (φ ∧ ψ) ⟶ (▶ φ ∧ ▶ ψ)
▶-∧-distr {φ} {ψ} = pair {▶ φ} {▶ ψ} {▶ (φ ∧ ψ)}
                    (mon {φ ∧ ψ} {φ} (π₁ {φ} {ψ}))
                    (mon {φ ∧ ψ} {ψ} (π₂ {φ} {ψ}))

▶-pres-∧ : {φ ψ : IPred} → (▶ φ ∧ ▶ ψ) ⟶ ▶ (φ ∧ ψ)
▶-pres-∧ zero     p = tt
▶-pres-∧ (suc n)  p = p


▷ : {ar : Arity} → IRel ar → IRel ar
▷ {ar} (iRel R decR) = iRel ▷R dec
  where
    ▷R : IRel₀ ar
    ▷R zero     = Top
    ▷R (suc n)  = R n

    dec : {n m : ℕ} → m ≤ n → ▷R n ⊆ ▷R m
    dec {n}         {.0}        z≤n        = Top! (▷R n)
    dec {.(suc _)}  {.(suc _)}  (s≤s m≤n)  = decR m≤n

\end{code}

Löb induction
\begin{code}
löb : {φ : IPred} → (▶ φ ⇒ φ) ⟶ φ
löb      zero     p = p zero z≤n tt
löb {φ}  (suc n)  p =
  p (suc n) ≤-refl (löb {φ} n (λ m m≤n ▶φm → p m (≤-step m≤n) ▶φm))
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
                (LiftT (CompatUpTo.tech F) (▷ Seq)) ≼ (▷ Seq)
  compat-step F zero     = Top! (CompatUpTo.trans F Top)
  compat-step F (suc n)  = compat-seq F n

  compat-∈-step : (F : CompatUpTo T) (ts : Terms ar) →
                  ▶ (ts ∈ LiftT (CompatUpTo.tech F) Seq) ⟶ ▶ (ts ∈ Seq)
  compat-∈-step F ts =
    mon {ts ∈ LiftT (CompatUpTo.tech F) Seq} {ts ∈ Seq} (compat-∈ F ts)

  -- compat-∈-step' : (F : CompatUpTo T) (ts : Terms ar) →
  --                  ▶ (ts ∈ Seq) ⟶  ▶ (CompatUpTo.trans F ts ∈ Seq)
  -- compat-∈-step' = ?
\end{code}

TODO:
* Extend up-to techniques to transformations of arbitrary arity;
  this is needed, for instance, for transitivity
* Example 1: Bisimilarity for streams + proof that ⊕ is commutative
* Example 2: Selection is homomorphism
* Example 3: Observational equivalence (do we need indexed relations?)
