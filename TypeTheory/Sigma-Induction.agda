{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality as P

data Phantom {i} {A : Set i} (a : A) : Set where
  phantom : Phantom a

module _ where
  private
    data #Σ-aux (A : Set) (B : A → Set) : Set where
      #pair : (x : A) → B x → #Σ-aux A B

  Σ : (A : Set) → (A → Set) → Set
  Σ A B = #Σ-aux A B

  pair : ∀ {A : Set} {B : A → Set} (x : A) → B x → Σ A B
  pair = #pair

  module ΣElim {A} {B} {S : Σ A B → Set}
    (pair* : ∀(a : A) (b : B a) → S (pair a b))
    where
      f-aux : Phantom pair* → (x : Σ A B) → S x
      f-aux x (#pair a b) = pair* a b

      f : (x : Σ A B) → S x
      f = f-aux phantom

open ΣElim public renaming (f to Σ-elim)

Σ-rec : ∀ {A} {B} {S : Set} → ((x : A) → B x → S) → Σ A B → S
Σ-rec f = Σ-elim f

isΣ-hom : ∀ {A B} {S : Set} (α : (a : A) → B a → S) →
          (Σ A B → S) → Set
isΣ-hom α f = ∀ a b → f (pair a b) ≡ α a b

Σ-rec-unique : ∀ {A B S} {α : (a : A) → B a → S} {f : Σ A B → S} → isΣ-hom α f →
               ∀ x → f x ≡ Σ-rec α x
Σ-rec-unique f-hom = Σ-elim f-hom

π₁ : ∀ {A B} → Σ A B → A
π₁ = Σ-rec (λ a _ → a)

π₂ : ∀ {A B} → (x : Σ A B) → B (π₁ x)
π₂ = Σ-elim (λ a b → b)

record ΣRecStruct (A : Set) (B : A → Set) : Set₁ where
  field
    Carrier : Set
    inj : (a : A) → B a → Carrier
    rec : ∀{S : Set} → ((a : A) → B a → S) → Carrier → S
    rec-hom : ∀ {S : Set} (α : (a : A) → B a → S) →
                 (∀ a b → rec α (inj a b) ≡ α a b)
    rec-unique : ∀ {S : Set} {α : (a : A) → B a → S} {f : Carrier → S} →
                 (∀ a b → f (inj a b) ≡ α a b) →
                 ∀ x → f x ≡ rec α x
-- open ΣRecStruct public

Σ-ΣRecStruct : ∀ A B → ΣRecStruct A B
Σ-ΣRecStruct A B = record
  { Carrier = Σ A B
  ; inj = pair
  ; rec = Σ-rec
  ; rec-hom = λ α a b → refl
  ; rec-unique = Σ-rec-unique
  }

ΣRecStruct-HasInduction : ∀{A B} → ΣRecStruct A B → Set₁
ΣRecStruct-HasInduction {A} {B} R =
  ∀ {S : Carrier → Set} (inj* : ∀(a : A) (b : B a) → S (inj a b)) →
  (x : Carrier) → S x
  where open ΣRecStruct R


-- I don't think that this is provable without resorting to π₂.
-- But I also conjecture that internally the negation is neither
-- provable.
∀ΣRecStruct-haveInduction : ∀{A B} (R : ΣRecStruct A B) →
                            ΣRecStruct-HasInduction R
∀ΣRecStruct-haveInduction R {S} inj* x = {!!}
  where
    open ΣRecStruct R

    S-aux : Set
    S-aux = Σ Carrier S

    f : Carrier → S-aux
    f = rec (λ a b → pair (inj a b) (inj* a b))
