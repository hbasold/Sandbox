module InfConj where

open import Data.Bool
open import Data.Sum
open import Relation.Binary.PropositionalEquality

record Stream (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : Stream A
open Stream public

-- | Partial elements
record D (A : Set) : Set where
  coinductive
  field step : A ⊎ D A
open D public

-- | Lift ⊎ to relations
data _⊎'_ {A B : Set} (R : A → A → Set) (S : B → B → Set) : A ⊎ B → A ⊎ B → Set where
  inj₁' : {x y : A} → R x y → (R ⊎' S) (inj₁ x) (inj₁ y)
  inj₂' : {x y : B} → S x y → (R ⊎' S) (inj₂ x) (inj₂ y)

-- | Bisimilarity for partial elements
record _~_ {A : Set} (x y : D A) : Set where
  coinductive
  field step~ : (_≡_ ⊎' _~_) (x .step) (y .step)
open _~_ public

-- | Injection into D
η : {A : Set} → A → D A
η a .step = inj₁ a

-- | Conjunction for partial Booleans
_∧'_ : D Bool → D Bool → D Bool
(x ∧' y) .step with x .step  | y .step
(x ∧' y) .step | inj₁ false  | v           = inj₁ false
(x ∧' y) .step | inj₁ true   | v           = v
(x ∧' y) .step | inj₂ x'     | inj₁ false  = inj₁ false
(x ∧' y) .step | inj₂ x'     | inj₁ true   = inj₂ x'
(x ∧' y) .step | inj₂ x'     | inj₂ y'     = inj₂ (x' ∧' y')

-- | Infinite conjunction
⋀∞ : Stream Bool → D Bool
⋀∞ s .step with s .hd
⋀∞ s .step | false = inj₁ false
⋀∞ s .step | true = inj₂ (⋀∞ (s .tl))

-- | Constant stream
K : {A : Set} → A → Stream A
K a .hd = a
K a .tl = K a

-- | Non-terminating computation
⊥ : {A : Set} → D A
⊥ .step = inj₂ ⊥

-- | Infinite conjunction of constant stream does not terminate
prop : ⋀∞ (K true) ~ ⊥
prop .step~ = inj₂' prop

-- | If there is an entry "false" in the stream, then the infinite conjunction
-- terminates. Here is just an example.
ex : ⋀∞ (false ∷ K true) ~ η false
ex .step~ = inj₁' refl
