{-# OPTIONS --sized-types #-}

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
record T∞ {i : Size} (C : Cont) : Set where
  coinductive
  field
    out : ∀ {j : Size< i} → • ⊎ ⟪ C ⟫ (T∞ {j} C)
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
c≢f x p = lem x (cong (λ t → out t {∞}) p)
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

-------------------------------------------
------- From example
-------------------------------------------

-- | The signature has two symbols: S of arity 1 and cons of arity 2.
sig₂ : Cont
sig₂ = cont (⊤ ⊎ ⊤) ar₂
  where
    ar₂ : ⊤ ⊎ ⊤ → Set
    ar₂ (inj₁ tt) = Fin 1
    ar₂ (inj₂ tt) = Fin 2

-- | Easier to read symbol names
S' cons' : Pos sig₂
S'    = inj₁ tt
cons' = inj₂ tt

-- | Tree constructors for S
S : ∀{i} → T∞ {i} sig₂ → T∞ {i} sig₂
out (S x) = inj₂ (S' , (λ _ → x))

-- | Tree constructors for cons
cons : T∞ sig₂ → T∞ sig₂ → T∞ sig₂
out (cons x y) = inj₂ (cons' , α)
  where
    α : Sh sig₂ cons' → T∞ sig₂
    α zero    = x
    α (suc _) = y

-- | Coinductive conlusion for the rule
-- from(S x, y) ⇒ from(x, cons (x, y)).
-- Note that we need to encode this as
-- from(S x, y) ∧ x ≡ x' ⇒ from(x, cons (x', y)).
From-Enc : (T∞ sig₂ → T∞ sig₂ → Set) → T∞ sig₂ → T∞ sig₂ → Set
From-Enc G x y with (out y)
... | inj₁ tt            = ⊥ -- no clause for from(x, •)
... | inj₂ (inj₁ tt , _) = ⊥ -- neither for from(x, S y)
... | inj₂ (inj₂ tt , α) =   -- from(S x, y) ∧ x ≡ x' ⇒ from(x, cons (x', y))
  let x' = α zero
      y  = α (suc zero)
  in x ≡ x' × G (S x) y

-- | Define From as coinductive relation.
record From (x y : T∞ sig₂) : Set where
  coinductive
  field
    out-From : From-Enc From x y
open From

----- Below, we construct for each x : T∞ sig₂ a term tₓ that is related to x
----- via From, and prove that this is indeed the case.

-- | t x = cons x (cons (s x) ...
t : T∞ sig₂ → T∞ sig₂
out (t x) = inj₂ (cons' , α)
  where
    α : Sh sig₂ cons' → T∞ sig₂
    α zero    = x
    α (suc _) = t (S x)

-- | Prove that x and tₓ are related via From.
lem : (x : T∞ sig₂) → From x (t x)
out-From (lem x) = (refl , lem (S x))

-- | From is inhabitated if T∞ sig₂ is.
thm : (x : T∞ sig₂) → ∃ λ y → From x y
thm x = , (lem x)

----------------------------------------
-- Different approach to show that From is inhabited:
-- The separate definition of T∞ and From makes it impossible, or at least
-- extremly difficult, to construct y and From x y at the same time.
-- The predicate ∃-From x thus simultaneously defines a special existential
-- quantifier for T∞ sig₂ that ensures that the given witness y fulfills
-- From x y.
-- Note that elements of ∃-From contain a lot of junk, as we always just use
-- the root of a tree. This make the first projection rather complicated, see
-- p₁. I guess, this could be made more economical.

∃-From-Enc : ∀{i} → (T∞ {i} sig₂ → Set) → T∞ {i} sig₂ → Set
∃-From-Enc {i} G x = Σ (⟪ sig₂ ⟫ (T∞ sig₂)) m
  where
    m : ⟪ sig₂ ⟫ (T∞ {i} sig₂) → Set
    m (inj₁ tt , _) = ⊥
    m (inj₂ tt , α) =
      let x' = α zero
          y  = α (suc zero)
      in x ≡ x' × G (S x)

record ∃-From {i : Size} (x : T∞ {i} sig₂) : Set where
  coinductive
  field
    out-∃-From : {j : Size< i} → ∃-From-Enc (∃-From {j}) x
open ∃-From

postulate
  T∞-ext : ∀{C} → (x y : T∞ C) → out x ≡ out y → x ≡ y

-- | Project out the witness.
p₁ : ∀ {i x} → ∃-From {i} x → T∞ {i} sig₂
out (p₁ u) {j} with out-∃-From u
... | (inj₁ tt , _) , ()
... | (inj₂ tt , α) , q , u' = inj₂ (cons' , α')
  where
    t' = p₁ u'
    α' : Fin 2 → T∞ {j} sig₂
    α' zero    = α zero
    α' (suc _) = t'

p₂ : ∀ {x} → (u : ∃-From x) → From x (p₁ u)
out-From (p₂ {x} u) = {!!}
  where
    m : (v : ∃-From-Enc ∃-From x) → v ≡ out-∃-From u → From-Enc From x (p₁ u)
    m v p with v
    ... | ((inj₁ tt , _) , ())
    ... | ((inj₂ tt , α) , q , u') = {!!} -- subst (From-Enc From x) s m'
      where
        v' : From (S x) (p₁ u')
        v' = p₂ u'

        α' : Fin 2 → T∞ sig₂
        α' zero    = α zero
        α' (suc _) = p₁ u'

        s : ∀ {α q u'} → ((inj₂ tt , α) , q , u') ≡ out-∃-From u →
            record { out = inj₂ (cons' , α') } ≡ p₁ u
        s p with out-∃-From u
        s p | r = {!!}

{-
        s p with out-∃-From u
        s p | (inj₁ tt , _) , ()
        s p | ((inj₂ tt , α₁) , q₁ , u'₁) = ?
        --  T∞-ext (record { out = inj₂ (cons' , α') }) (p₁ u) {!!}
-}

        m' : From-Enc From x (record { out = inj₂ (cons' , α') })
        m' = (q , v')

thm₂ : ∀{i} → (x : T∞ {i} sig₂) → ∃-From {i} x
out-∃-From (thm₂ {i} x) {j} = ((cons' , α) , refl , u)
  where
    u = thm₂ {j} (S x)

    α : Sh sig₂ cons' → T∞ {j} sig₂
    α zero    = x
    α (suc _) = p₁ u

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
