\begin{code}
{-# OPTIONS --without-K #-}
\end{code}

\begin{code}
module CoindLog where

open import Data.List
open import Data.Nat hiding (pred)
open import Data.Nat.Properties
open import Data.Unit hiding (_≤_)
open import Data.Product
open import Function
\end{code}

In the following, we define relations of arbitrary arity.
These subsume sets (0-ary relations) and predicates (1-ary relations).
\begin{code}
Arity : Set₁
Arity = List Set

Rel : Arity → Set₁
Rel [] = Set
Rel (X ∷ Xs) = X → Rel Xs

_⊆_ : {ar : Arity} → Rel ar → Rel ar → Set
_⊆_ {[]} R S = R → S
_⊆_ {X ∷ ar} R S = ∀ (x : X) → R x ⊆ S x

⊆-trans : {ar : Arity} {R S T : Rel ar} →
          R ⊆ S → S ⊆ T → R ⊆ T
⊆-trans {[]}     p q = q ∘ p
⊆-trans {X ∷ ar} p q = λ x → ⊆-trans {ar} (p x) (q x)
\end{code}

Full relation
\begin{code}
Top : {ar : Arity} → Rel ar
Top {[]} = ⊤
Top {X ∷ ar} x = Top {ar}

Top! : {ar : Arity} → (R : Rel ar) → R ⊆ Top
Top! {[]} R = λ x → tt
Top! {X ∷ ar} R = λ x → Top! (R x)
\end{code}

Next, we introduce relation transformer, which are monotone functions on
the lattice of relations.
\begin{code}
RelT₀ : (ar : Arity) → Set₁
RelT₀ ar = Rel ar → Rel ar

record RelT (ar : Arity) : Set₁ where
  constructor relT
  field
    trans  : RelT₀ ar
    mono   : ∀ R S → R ⊆ S → trans R ⊆ trans S

_⊑_ : {ar : Arity} → RelT ar → RelT ar → Set₁
(relT F _) ⊑ (relT G _) = ∀ R → F R ⊆ G R

_⊚_ : {ar : Arity} → RelT ar → RelT ar → RelT ar
(relT G monoG) ⊚ (relT F monoF) = relT (G ∘ F) mono
  where
    mono : (R S : Rel _) → R ⊆ S → G (F R) ⊆ G (F S)
    mono R S p = monoG (F R) (F S) (monoF R S p)
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
_∈'_ {[]} ts R = R
_∈'_ {X ∷ ar} (t , ts) R = ts ∈' R t

∈-mono : {ar : Arity} (R S : Rel ar) (ts : Terms ar) → R ⊆ S → ts ∈' R → ts ∈' S
∈-mono {[]}    R S ts       p q = p q
∈-mono {x ∷ ar} R S (t , ts) p q = ∈-mono (R t) (S t) ts (p t) q

Top-∈ : {ar : Arity} → (ts : Terms ar) → ts ∈' Top
Top-∈ {[]}    _        = tt
Top-∈ {x ∷ ar} (t , ts) = Top-∈ ts
\end{code}

Indexed relations
\begin{code}
IRel₀ : Arity → Set₁
IRel₀ ar = ℕ → Rel ar

record IRel (ar : Arity) : Set₁ where
  constructor iRel
  field
    rel : IRel₀ ar
    dec : ∀ n m → m ≤ n → rel n ⊆ rel m

_≼_ : {ar : Arity} → IRel ar → IRel ar → Set
(iRel R _) ≼ (iRel S _) = ∀ n → R n ⊆ S n

LiftT : {ar : Arity} → RelT ar → IRel ar → IRel ar
LiftT {ar} (relT Φ mono) (iRel R decR) = iRel ΦR dec
  where
    ΦR : IRel₀ ar
    ΦR n = Φ (R n)

    dec : (n m : ℕ) → m ≤ n → ΦR n ⊆ ΦR m
    dec n m p = mono (R n) (R m) (decR n m p)
\end{code}

Indexed predicates
\begin{code}
IPred₀ : Set₁
IPred₀ = ℕ → Set

record IPred : Set₁ where
  constructor iPred
  field
    pred : IPred₀
    dec : ∀ n m → m ≤ n → pred n → pred m

_∈₀_ : {ar : Arity} → Terms ar → IRel₀ ar → IPred₀
(ts ∈₀ R) n = ts ∈' R n

_∈_ : {ar : Arity} → Terms ar → IRel ar → IPred
ts ∈ (iRel R decR) = iPred (ts ∈₀ R) dec
  where
    dec : (n m : ℕ) → m ≤ n → ts ∈' R n → ts ∈' R m
    dec n m m≤n p = ∈-mono (R n) (R m) ts (decR n m m≤n) p

_⇒₀_ : IPred₀ → IPred₀ → IPred₀
(φ ⇒₀ ψ) n = ∀ m → m ≤ n → φ m → ψ m

_⇒_ : IPred → IPred → IPred
(iPred φ decφ) ⇒ (iPred ψ decψ) = iPred (φ ⇒₀ ψ) dec
  where
    dec : (n m : ℕ) → m ≤ n → (φ ⇒₀ ψ) n → (φ ⇒₀ ψ) m
    dec n m m≤n p k k≤m q = decψ k k ≤-refl (p k (≤-trans k≤m m≤n) q)

_⟶_ : IPred → IPred → Set
(iPred φ _) ⟶ (iPred ψ _) = ∀ n → φ n → ψ n

≼→∈ : {ar : Arity} {R S : IRel ar} → R ≼ S → ∀ ts → (ts ∈ R) ⟶ (ts ∈ S)
≼→∈ p ts n q = ∈-mono _ _ ts (p n) q
\end{code}

Later modality for indexed predicates
\begin{code}
▶ : IPred → IPred
▶ (iPred φ decφ) = iPred ▶φ dec
  where
    ▶φ : IPred₀
    ▶φ zero = ⊤
    ▶φ (suc n) = φ n

    dec : (n m : ℕ) → m ≤ n → ▶φ n → ▶φ m
    dec n        .0        z≤n      p = tt
    dec .(suc _) .(suc _) (s≤s m≤n) p = decφ _ _ m≤n p

next : {φ : IPred} → φ ⟶ ▶ φ
next                zero    p = tt
next {iPred φ decφ} (suc n) p = decφ (1 + n) n (n≤1+n n) p

mon : {φ ψ : IPred} → (φ ⟶ ψ) → (▶ φ ⟶ ▶ ψ)
mon p zero    q = tt
mon p (suc n) q = p n q
\end{code}

Löb induction
\begin{code}
löb : {φ : IPred} → (▶ φ ⇒ φ) ⟶ φ
löb     zero     p = p zero z≤n tt
löb {φ} (suc n)  p =
  p (suc n) ≤-refl (löb {φ} n (λ m m≤n ▶φm → p m (≤-step m≤n) ▶φm))
\end{code}

\begin{code}
module ChainReasoning {ar : Arity} (T : RelT ar) where
  open RelT T renaming (trans to Φ; mono to monoΦ)

  \end{code}

  Final chain for a monotone operator and the associated
  \begin{code}
  Seq₀ : IRel₀ ar
  Seq₀ zero = Top
  Seq₀ (suc n) = Φ (Seq₀ n)

  Seq : IRel ar
  Seq = iRel Seq₀ dec
    where
      dec : (n m : ℕ) → m ≤ n → Seq₀ n ⊆ Seq₀ m
      dec n        .0        z≤n     = Top! (Seq₀ n)
      dec (suc n)  (suc m)  (s≤s p)  = monoΦ (Seq₀ n) (Seq₀ m) (dec _ _ p)
\end{code}

Unfolding of the operator on the sequence.
This will allow us to do recursion steps with the Löb rule.
\begin{code}
  seq : (ts : Terms ar) → ▶ (ts ∈ LiftT T Seq) ⟶ (ts ∈ Seq)
  seq ts zero    p = Top-∈ ts
  seq ts (suc n) p = p
\end{code}

Compatible up-to techniques give us inclusions on every step of the
sequence.
This will allow us to import them into recursive proofs.
\begin{code}
  compat-seq : (F : CompatUpTo T) → (LiftT (CompatUpTo.tech F) Seq) ≼ Seq
  compat-seq F zero = Top! (CompatUpTo.trans F Top)
  compat-seq F (suc n) =
    ⊆-trans {ar}
            (compat (Seq₀ n))
            (monoΦ (LiftT tech Seq .IRel.rel n) (Seq₀ n) (compat-seq F n))
    where
      open CompatUpTo F renaming (trans to Ψ)

  compat-∈ : (F : CompatUpTo T) (ts : Terms ar) →
             (ts ∈ LiftT (CompatUpTo.tech F) Seq) ⟶ (ts ∈ Seq)
  compat-∈ F ts n p =
    ≼→∈ {ar} {LiftT (CompatUpTo.tech F) Seq} {Seq} (compat-seq F) ts n p
\end{code}

TODO:
* Extend up-to techniques to transformations of arbitrary arity;
  this is needed, for instance, for transitivity
* Example 1: Bisimilarity for streams + proof that ⊕ is commutative
* Example 2: Selection is homomorphism
* Example 3: Observational equivalence (do we need indexed relations?)
