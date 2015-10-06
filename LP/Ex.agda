{-# OPTIONS --sized-types --without-K #-}

module Ex where

open import Size
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Fin
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

• : Set
• = ⊤

-- | Container for defining signatures
record Cont : Set₁ where
  constructor cont
  field
    Pos : Set
    Sh : Pos → Set
open Cont

-- | Extension of a container
⟪_⟫ : Cont → Set → Set
⟪ cont P S ⟫ X = Σ P (λ p → S p → X)

-- | Finite and infinite trees over a signature
record T∞ (C : Cont) : Set where
  coinductive
  field
    out : • ⊎ ⟪ C ⟫ (T∞ C)
open T∞

------
-- Example due to Fu Peng
-----

-- In the following, we give two interpretations to the logic program
-- ⇒ P(c)
-- P(x), P(f(f x)) ⇒ P(f x).
-- The first is an inductive interpretation, the second is coinductive.
-- In both cases we are able to prove that there is a tree x : Tree sig₁,
-- such that P x holds.

-- | Signature has two symbols, a nullary and a unary symbol.
sig₁ : Cont
sig₁ = cont (⊤ ⊎ ⊤) S
  where
    S : ⊤ ⊎ ⊤ → Set
    S (inj₁ tt) = Fin 0
    S (inj₂ tt) = Fin 1

-- | Symbol names
c' f' : Pos sig₁
c' = inj₁ tt
f' = inj₂ tt

-- | Symbol constructor for c
c : T∞ sig₁
out c = inj₂ (c' , (λ ()))

-- | Constructor for symbol f
f : T∞ sig₁ → T∞ sig₁
out (f x) = inj₂ (f' , (λ _ → x))

-- | c and f a distinct constructors
c≢f : (x : T∞ sig₁) → c ≡ f x → ⊥
c≢f x p = lem x (cong out p)
  where
    lem : (y : T∞ sig₁) → out c ≡ out (f y) → ⊥
    lem y ()

-- | Inductive interpretation of LP
data P-ind : T∞ sig₁ → Set where
  c-P : P-ind c
  f-P : (x : T∞ sig₁) → P-ind x → P-ind (f (f x)) → P-ind (f x)

-- | P c holds immediately.
p-ind₀ : ∃ λ x → P-ind x
p-ind₀ = (c , c-P)

unprvbl-lem : (x : T∞ sig₁) → P-ind (f x) → ⊥
unprvbl-lem x q = m x (f x) q refl
  where
    m : (x y : T∞ sig₁) → P-ind y → y ≡ f x → ⊥
    m x .c c-P p = (c≢f x p)
    m x .(f x₁) (f-P x₁ p q₁) e = m (f x₁) (f (f x₁)) q₁ refl

-- | We can show that there is no tree x, s.t. P-ind (f x) holds.
unprvbl : ¬ (∃ λ x → P-ind (f x))
unprvbl (x , q) = unprvbl-lem x q

-------
-- Coinductive interpretation of LP

F : (T∞ sig₁ → Set) → T∞ sig₁ → Set
F G x = m (out x)
  where
    m : ⊤ ⊎ ⟪ sig₁ ⟫ (T∞ sig₁) → Set
    m (inj₁ tt) = ⊥            -- case for •
    m (inj₂ (inj₁ tt , _)) = ⊤ -- case for c, k₀
    m (inj₂ (inj₂ tt , α)) =   -- case for f x, k₁
      let x = α zero
      in G x × G (f (f x))

record P-coind' (x : T∞ sig₁) : Set where
  coinductive
  field
    p-out' : F P-coind' x
open P-coind'


record P-coind {i : Size} (x : T∞ sig₁) : Set where
  coinductive
  field
    p-out : ∀ {j : Size< i} → F (P-coind {j}) x
open P-coind

-- | Trivial proof
k₀ : P-coind c
p-out k₀ = tt

-- | Non-trivial proof
p-coind : ∃ λ x → P-coind (f x)
p-coind = (_ , k _ k₀)
  where
    k : ∀{i} → (x : T∞ sig₁) → P-coind {i} x → P-coind {i} (f x)
    p-out (k x q) = (q , k (f x) (k x q))

----------

sig₂ : Cont
sig₂ = cont (⊤ ⊎ ⊤) ar₂
  where
    ar₂ : ⊤ ⊎ ⊤ → Set
    ar₂ (inj₁ tt) = Fin 1
    ar₂ (inj₂ tt) = Fin 2

S' cons' : Pos sig₂
S'    = inj₁ tt
cons' = inj₂ tt

S : T∞ sig₂ → T∞ sig₂
out (S x) = inj₂ (S' , (λ _ → x))

cons : T∞ sig₂ → T∞ sig₂ → T∞ sig₂
out (cons x y) = inj₂ (cons' , α)
  where
    α : Sh sig₂ cons' → T∞ sig₂
    α zero    = x
    α (suc _) = y

From-Enc : (T∞ sig₂ → T∞ sig₂ → Set) → T∞ sig₂ → T∞ sig₂ → Set
From-Enc G x y with (out y)
... | inj₁ x₁ = ⊥ -- •
... | inj₂ (inj₁ tt , _) = ⊥ -- S
... | inj₂ (inj₂ tt , α) =   -- cons (x', y)
  let x' = α zero
      y  = α (suc zero)
  in x ≡ x' → G (S x) y
  where

record From (x y : T∞ sig₂) : Set where
  coinductive
  field
    out-From : Frodm-Enc From x y
open From

thm : (x : T∞ sig₂) → ∃ λ y → From x y
thm x = ({!!} , {!!})
  where
    q : From x _
    out-From q = {!!}

---------------------
-- Some other tries
--------------------
{-
F : (ℕ → Set) → ℕ → Set
F G 0       = ⊤
F G (suc n) = G n

record NatLp (n : ℕ) : Set where
  coinductive
  field
    out : F NatLp n
open NatLp

lem : (n : ℕ) → NatLp n
out (lem zero)    = tt
out (lem (suc n)) = lem n

record bad (A : Set) (a : A) : Set where
  coinductive
  field
    bad-out : bad A a
open bad

bad-lem : (n : ℕ) → bad ℕ n
bad-out (bad-lem n) = bad-lem n

-}
