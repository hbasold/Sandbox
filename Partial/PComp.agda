{-# OPTIONS --without-K #-}

module PComp where

open import Data.Empty
open import Data.Sum
open import Data.Nat as Nat
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties
open import Data.Product
open import Data.Bool renaming (Bool to 𝔹)
open import Data.Bool.Properties
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Relation.Binary
open DecTotalOrder Nat.decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)

-- open import Size

-- record D {i : Size} (A : Set) : Set where
--   coinductive
--   field step : {j : Size< i} → A ⊎ D {j} A

-- open D public

-- μ' : ∀{i} → (ℕ → 𝔹) → ℕ → D {i} ℕ
-- μ' p n .step = if p n then inj₁ n else inj₂ (μ' p (suc n))

primRec : {X Y : Set} → (X → Y) → (ℕ → Y → X → Y) → ℕ → X → Y
primRec f g zero    x = f x
primRec f g (suc n) x = g n (primRec f g n x) x

record D (A : Set) : Set where
  coinductive
  field step : A ⊎ D A

open D public

μ' : (ℕ → 𝔹) → ℕ → D ℕ
c : (ℕ → 𝔹) → ℕ → 𝔹 → ℕ ⊎ (D ℕ)

μ' p n .step = c p n (p n)

c p n false = inj₂ (μ' p (1 + n))
c p n true  = inj₁ n

μ : (ℕ → 𝔹) → D ℕ
μ p = μ' p 0

isEven : ℕ → 𝔹
isEven zero = true
isEven (suc zero) = false
isEven (suc (suc n)) = isEven n

data _↓_ {A : Set} (d : D A) (a : A) : Set where
  now    :                d .step ≡ inj₁ a            → d ↓ a
  later  : {d' : D A} →  d .step ≡ inj₂ d' → d' ↓ a  → d ↓ a

foo : μ' isEven 3 ↓ 4
foo = later (cong inj₂ refl) (now refl)

μ-finds-tt : ∀{p : ℕ → 𝔹} {m n : ℕ} → μ' p m ↓ n → p n ≡ true
μ-finds-tt {p} {m} (now q)        with p m  | inspect p m
μ-finds-tt {p} {m} (now ())        | false  | _
μ-finds-tt {p} {m} (now refl)      | true   | [ eq ]       = eq
μ-finds-tt {p} {m} (later q t)    with p m
μ-finds-tt {p} {m} (later refl t)  | false = μ-finds-tt t
μ-finds-tt {p} {m} (later () t)    | true

-- | Compute the number of steps taken to obtain p n = tt.
μ-dist : ∀{p : ℕ → 𝔹} {m n : ℕ} → μ' p m ↓ n → ∃ λ k → n ≡ m + k
μ-dist {p} {m} (now q)        with p m
μ-dist {p} {m} (now ())        | false
μ-dist {p} {m} (now refl)      | true = (0 , sym (+-right-identity m))
μ-dist {p} {m} (later q t)    with p m
μ-dist {p} {m} (later refl t)  | false =
  let (k , e) = μ-dist t
  in (1 + k , trans e (sym (+-suc m k)))
μ-dist {p} {m} (later () t)    | true

empty-interval : ∀ {m k} → m ≤ k → k < m → ⊥
empty-interval z≤n ()
empty-interval (s≤s p) (s≤s q) = empty-interval p q

suc≤⇒≤ : ∀ m n → suc m ≤ n → m ≤ n
suc≤⇒≤ m zero ()
suc≤⇒≤ .0 (suc n) (s≤s z≤n) = z≤n
suc≤⇒≤ .(suc _) (suc .(suc _)) (s≤s (s≤s p)) = s≤s (suc≤⇒≤ _ _ (s≤s p))

-- | The proof proceeds by induction on the termination proof t : μ' p m ↓ n.
-- In the process, we first distinguishing whether m = k or m < k.
-- Next, we check whether the computation has termination, that is, whether
-- t = now ... or t = later.
-- Finally, we distinguish on the values of p m, which allows us to make
-- a computation step with μ'. The other cases follow then from there.
μ-min : ∀{p : ℕ → 𝔹} {m n : ℕ} → μ' p m ↓ n → ∀ k → m ≤′ k → k < n → p k ≡ false
-- m = k
---- t = now
μ-min {p} {.m} (now q)       m ≤′-refl u with p m
μ-min {p} {.m} (now q)       m ≤′-refl u | false = refl
μ-min {p} {.m} (now refl)    m ≤′-refl u | true  = ⊥-elim (1+n≰n u)

-- m = k
---- t = later
μ-min {p} {.m} (later q t)   m ≤′-refl u with p m
μ-min {p} {.m} (later q t)   m ≤′-refl u | false = refl
μ-min {p} {.m} (later () t)  m ≤′-refl u | true

-- m < k
---- t = now
μ-min {p} {m}        (now q)    .(suc _) (≤′-step l) u    with p m
μ-min {p} {m}        (now ())   .(suc _) (≤′-step l) u       | false
μ-min {p} {.(suc _)} (now refl) .(suc _) (≤′-step l) (s≤s u) | true =
  ⊥-elim (empty-interval (suc≤⇒≤ _ _ (≤′⇒≤ l)) u)

-- m < k
---- t = later
μ-min {p} {m} (later q    t) .(suc _) (≤′-step {k'} l) u with p m
μ-min {p} {m} (later refl t) .(suc _) (≤′-step {k'} l) u    | false =
  μ-min t (suc k') (s≤′s l) u
μ-min {p} {m} (later ()   t) .(suc n) (≤′-step {n} l)  u    | true

Min : (ℕ → Set) → ℕ → Set
Min P n = P n × ∀ k → k < n → ¬ (P k)

-- | Definition of partial correctness for the μ-operator.
-- This states that if μ p terminates with n as result, then n is the
-- minimal number, for which p n ≡ true.
PartialCorrectness : Set
PartialCorrectness = ∀{p : ℕ → 𝔹} {n : ℕ} →
  μ p ↓ n → Min (λ k → p k ≡ true) n

μ-pcorrect : PartialCorrectness
μ-pcorrect t = (μ-finds-tt t , (λ k u → not-¬ (μ-min t k (z≤′n) u)))

-- Correctness : Set
-- Correctness = ∀{p : ℕ → 𝔹} →
--   ¬(∃ λ n → μ p ↓ n) → ∀ n → ¬(p n ≡ true)

-- find-min' : ∀{p : ℕ → 𝔹} → ∀ n → p n ≡ true → (m : ℕ) → m ≤ n →
--             (∃ λ k → k ≤ n × p k ≡ true)
-- find-min' {p} last pt zero l with p 0 | inspect p 0
-- find-min' {p} last pt zero l | false | e = (last , ≤-refl , pt)
-- find-min' {p} last pt zero l | true | [ e ] = (zero , l , e)
-- find-min' {p} last pt (suc m) l with p m | inspect p m
-- find-min' {p} last pt (suc m) l | false | e =
--   find-min' last pt m (suc≤⇒≤ m last l)
-- find-min' {p} last pt (suc m) l | true | [ e ] =
--   let (k , k≤last , q) = find-min' {p} m e m ≤-refl
--   in (k , ≤-trans k≤last (suc≤⇒≤ m last l) , q)

-- find-min : ∀{p : ℕ → 𝔹} → ∀ n → p n ≡ true → (∃ λ k → k ≤ n × p k ≡ true)
-- find-min {p} n pt = find-min' {p} n pt n ≤-refl

-- min-terminate : ∀{p : ℕ → 𝔹} → ∀ n (e : p n ≡ true) (m : ℕ) → m ≤ n → ∃ λ k → μ p ↓ k
-- min-terminate {p} last pt zero m≤n with p 0 | inspect p 0
-- min-terminate {p} last pt zero m≤n | false | e = {!!} , {!!}
-- min-terminate {p} last pt zero m≤n | true | e = {!!}
-- min-terminate {p} last pt (suc m) m≤n = {!!}


-- lem : ∀{p : ℕ → 𝔹} → ∀ n → p n ≡ true → ∃ λ k → μ p ↓ k
-- lem {p} zero q with p 0   | inspect p 0
-- lem {p} zero () | false | _
-- lem {p} zero q | true | [ e ] = (0 , now (cong (c p 0) e))
-- lem {p} (suc n) q with p (suc n)   | inspect p (suc n)
-- lem {p} (suc n) () | false | e
-- lem {p} (suc n) q | true | e =
--   let (k , t) = lem n {!!}
--   in (suc n , now {!!})

-- μ-correct : Correctness
-- μ-correct q n pt = q (lem n pt)
