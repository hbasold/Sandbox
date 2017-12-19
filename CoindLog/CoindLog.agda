module CoindLog where

open import Data.List
open import Data.Nat hiding (pred)
open import Data.Nat.Properties
open import Data.Unit hiding (_≤_)
open import Data.Product

Rel : List Set → Set₁
Rel [] = Set
Rel (X ∷ Xs) = X → Rel Xs

_⊆_ : {L : List Set} → Rel L → Rel L → Set
_⊆_ {[]} R S = R → S
_⊆_ {X ∷ L} R S = ∀ (x : X) → R x ⊆ S x

RelT₀ : (L : List Set) → Set₁
RelT₀ L = Rel L → Rel L

record RelT (L : List Set) : Set₁ where
  constructor relT
  field
    trans  : RelT₀ L
    mono   : ∀ R S → R ⊆ S → trans R ⊆ trans S

Terms : List Set → Set
Terms [] = ⊤
Terms (X ∷ Xs) = X × Terms Xs

_∈'_ : {L : List Set} → Terms L → Rel L → Set
_∈'_ {[]} ts R = R
_∈'_ {X ∷ L} (t , ts) R = ts ∈' R t

∈-mono : {L : List Set} (R S : Rel L) (ts : Terms L) → R ⊆ S → ts ∈' R → ts ∈' S
∈-mono {[]}    R S ts       p q = p q
∈-mono {x ∷ L} R S (t , ts) p q = ∈-mono (R t) (S t) ts (p t) q

-- Rel₂ : Set → Set → Set₁
-- Rel₂ A B = Rel (A ∷ [ B ])

Top : {L : List Set} → Rel L
Top {[]} = ⊤
Top {X ∷ L} x = Top {L}

Top! : {L : List Set} → (R : Rel L) → R ⊆ Top
Top! {[]} R = λ x → tt
Top! {X ∷ L} R = λ x → Top! (R x)

Top-∈ : {L : List Set} → (ts : Terms L) → ts ∈' Top
Top-∈ {[]}    _        = tt
Top-∈ {x ∷ L} (t , ts) = Top-∈ ts

IRel₀ : List Set → Set₁
IRel₀ L = ℕ → Rel L

record IRel (L : List Set) : Set₁ where
  constructor iRel
  field
    rel : IRel₀ L
    dec : ∀ n m → m ≤ n → rel n ⊆ rel m

LiftT : {L : List Set} → RelT L → IRel L → IRel L
LiftT {L} (relT Φ mono) (iRel R decR) = iRel ΦR dec
  where
    ΦR : IRel₀ L
    ΦR n = Φ (R n)

    dec : (n m : ℕ) → m ≤ n → ΦR n ⊆ ΦR m
    dec n m p = mono (R n) (R m) (decR n m p)

IPred₀ : Set₁
IPred₀ = ℕ → Set

record IPred : Set₁ where
  constructor iPred
  field
    pred : IPred₀
    dec : ∀ n m → m ≤ n → pred n → pred m

Seq₀ : {L : List Set} → RelT₀ L → IRel₀ L
Seq₀ Φ zero = Top
Seq₀ Φ (suc n) = Φ (Seq₀ Φ n)

Seq : {L : List Set} → RelT L → IRel L
Seq (relT Φ mono) = iRel (Seq₀ Φ) dec
  where
    dec : (n m : ℕ) → m ≤ n → Seq₀ Φ n ⊆ Seq₀ Φ m
    dec n        .0        z≤n     = Top! (Seq₀ Φ n)
    dec (suc n)  (suc m)  (s≤s p)  = mono (Seq₀ _ n) (Seq₀ _ m) (dec _ _ p)

_∈₀_ : {L : List Set} → Terms L → IRel₀ L → IPred₀
(ts ∈₀ R) n = ts ∈' R n

_∈_ : {L : List Set} → Terms L → IRel L → IPred
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

▶ : IPred → IPred
▶ (iPred φ decφ) = iPred ▶φ dec
  where
    ▶φ : IPred₀
    ▶φ zero = ⊤
    ▶φ (suc n) = φ n

    dec : (n m : ℕ) → m ≤ n → ▶φ n → ▶φ m
    dec n        .0        z≤n      p = tt
    dec .(suc _) .(suc _) (s≤s m≤n) p = decφ _ _ m≤n p

löb : {φ : IPred} → (▶ φ ⇒ φ) ⟶ φ
löb     zero     p = p zero z≤n tt
löb {φ} (suc n)  p =
  p (suc n) ≤-refl (löb {φ} n (λ m m≤n ▶φm → p m (≤-step m≤n) ▶φm))

next : {φ : IPred} → φ ⟶ ▶ φ
next                zero    p = tt
next {iPred φ decφ} (suc n) p = decφ (1 + n) n (n≤1+n n) p

mon : {φ ψ : IPred} → (φ ⟶ ψ) → (▶ φ ⟶ ▶ ψ)
mon p zero    q = tt
mon p (suc n) q = p n q

seq : {L : List Set} {T : RelT L} (ts : Terms L) →
      ▶ (ts ∈ LiftT T (Seq T)) ⟶ (ts ∈ Seq T)
seq ts zero    p = Top-∈ ts
seq ts (suc n) p = p

-- TODO:
-- * Prove correctness for compatible up-to techniques
-- * Example 1: Bisimilarity for streams + proof that ⊕ is commutative
-- * Example 2: Selection is homomorphism
-- * Example 3: Observational equivalence (do we need indexed relations?)
