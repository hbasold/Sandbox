{-# OPTIONS --without-K --copatterns --sized-types #-}
open import lib.Basics
open import lib.PathGroupoid
open import lib.types.Paths
open import lib.Funext
open import Size


-- | Coinductive delay type. This is the functor νπ̂ : Set → Set arising
-- as the fixed point of π̂(H) = π ∘ ⟨Id, H⟩, where π : Set × Set → Set
-- with π(X, Y) = X.
record D (S : Set) : Set where
  coinductive
  field
    #force : S
open D

-- | Action of D on morphisms
D₁ : ∀ {X Y} → (X → Y) → D X → D Y
#force (D₁ f x) = f (#force x)

-- | D lifted to dependent functions
↑D₁ : ∀ {A} → (B : A → Set) → ((x : A) → B x) → (y : D A) → D (B (#force y))
#force (↑D₁ B f y) = f (#force y)

postulate
  -- | We'll need coinduction to prove such equalities in the future, or prove
  -- it from univalence.
  D-coind : ∀ {S} {x y : D S} → #force x == #force y → x == y

D-coind2 : ∀ {S} {x y : D S} → D (#force x == #force y) → x == y
D-coind2 p = D-coind (#force p)

module _ where
  private
    mutual
      data #P-aux (A : Set) : {i : Size} → Set where
        #now : {i : Size} → A → #P-aux A {↑ i}
        #later : {i : Size} → D (#P {i} A) → #P-aux A {↑ i}

      data #P {i : Size} (A : Set) : Set where
        #p : #P-aux A {i} → (Unit → Unit) → #P {i} A

  P : ∀{i : Size} → Set → Set
  P {i} A = #P {i} A

  ∞P : ∀{i : Size} → Set → Set
  ∞P {i} A = D (#P {i} A)

  now : ∀ {i} {A} → A → P {↑ i} A
  now a = #p (#now a) _

  later : ∀ {i} {A} → ∞P {i} A → P {↑ i} A
  later x = #p (#later x) _

  force : ∀ {i} {A} → ∞P {i} A → P {i} A
  force = #force

  postulate  -- HIT
    weak~ : ∀{A} → (x : ∞P A) → (later x == force x)

  -- | Extra module for recursion using sized types.
  -- This is convenient, as we can use the functor D in the definition, which
  -- in turn simplifies proofs.
  module PRec {A} {X : Set}
    (now* : A → X)
    (later* : D X → X)
    (weak~* : (x : D X) → (later* x == #force x))
    where
      f : ∀ {i} → P {i} A → X
      f = f-aux phantom where
        f-aux : ∀ {i} → Phantom weak~* → #P {i} A → X
        f-aux phantom (#p (#now a) _)        = now* a
        f-aux phantom (#p (#later {j} x') _) = later* (D₁ (f {j}) x')

  module PElim {A} {S : P A → Set}
    (now* : ∀(a : A) → S (now a))
    (later* : (x : ∞P A) → (x_rec : D (S (force x))) → S (later x))
    (weak~* : (x : ∞P A) → (x_rec : D (S (force x))) →
              (later* x x_rec == (#force x_rec) [ S ↓ (weak~ x) ]))
    where
      g-aux : Phantom weak~* → (y : ∞P A) → D (S (#force y))

      f-aux : Phantom weak~* → (x : P A) → S x
      f-aux phantom (#p (#now a) _)    = now* a
      f-aux phantom (#p (#later x') _)
        = later* x' (g-aux phantom x') -- (↑D₁ S f x')

      #force (g-aux phantom y) = f-aux phantom (#force y)

      g : (y : ∞P A) → D (S (#force y))
      g = g-aux phantom

      f : (x : P A) → S x
      f = f-aux phantom

      f-homomorphism : (y : ∞P A) → f (later y) == later* y (↑D₁ S f y)
      f-homomorphism y =
          f (later y)
        =⟨ idp ⟩
          later* y (g y)
        =⟨ g-is-D₁f |in-ctx later* y ⟩
          later* y (↑D₁ S f y)
        ∎
        where
          lem : #force (g y) == #force (↑D₁ S f y)
          lem =
              #force (g y)
            =⟨ idp ⟩
              f (#force y)
            =⟨ idp ⟩
              #force (↑D₁ S f y)
            ∎

          g-is-D₁f : g y == ↑D₁ S f y
          g-is-D₁f = D-coind lem

      postulate      -- HIT
        weak~-β : (x : ∞P A) → apd f (weak~ x) == weak~* x (g x)

open PRec public using () renaming (f to P-rec)
open PElim public using ()
  renaming (f to P-elim; g to ∞P-elim; f-homomorphism to P-elim-hom)

module Bla where

-- | Action of P on morphisms
P₁ : ∀ {A B} → (A → B) → (P A → P B)
P₁ f = P-rec (now ∘ f) later weak~

-- | Unit for the monad
η : ∀ {A} → A → P A
η = now

-- | Monad multiplication
μ : ∀ {A} → P (P A) → P A
μ {A} = P-rec (idf (P A)) later weak~

-- | Direct definition of bind
bind : ∀ {A B} → (A → P B) → (P A → P B)
bind {A} {B} f = P-rec f later weak~

η-natural : ∀ {A B} → (f : A → B) →
            η ∘ f == P₁ f ∘ η
η-natural f = λ=-nondep (λ x → idp)
  where
    open FunextNonDep

μ-natural : ∀ {A B} → (f : A → B) →
            μ ∘ P₁ (P₁ f) == P₁ f ∘ μ
μ-natural {A} f = λ=-nondep q
  where
    open FunextNonDep

    T : P (P A) → Set
    T x = μ ( P₁ (P₁ f) x) == P₁ f (μ x)

    p : (x : ∞P (P A)) → D (T (force x)) → T (later x)
    p x dty =
        μ (P₁ (P₁ f) (later x))
      =⟨ idp ⟩
        μ (later (D₁ (P₁ (P₁ f)) x))
      =⟨ idp ⟩
        later (D₁ μ (D₁ (P₁ (P₁ f)) x))
      =⟨ D-coind2 dty |in-ctx later ⟩
         later (D₁ (P₁ f) (D₁ μ x))
      =⟨ idp ⟩
         P₁ f (later (D₁ μ x))
      =⟨ idp ⟩
         P₁ f (μ (later x))
      ∎

    r : (x : ∞P (P A)) → (x_rec : D (T (force x))) →
        (p x x_rec) == (#force x_rec) [ T ↓ (weak~ x) ]
    r x x_rec = {!!}

    q : (x : P (P A)) → μ ( P₁ (P₁ f) x) == P₁ f (μ x)
    q = P-elim
        {S = λ x → μ ( P₁ (P₁ f) x) == P₁ f (μ x)}
        (λ a → idp) p r

data _↓_ {A} : (P A) → A → Set where
  now↓ : (a : A) → now a ↓ a
  later↓ : (a : A) → (x : ∞P A) → (force x) ↓ a → (later x) ↓ a

mutual
  data ~proof {A} : P A → P A → Set where
    terminating : (a : A) (x y : P A) → x ↓ a → y ↓ a → ~proof x y
    step : (u v : ∞P A) → force u ~ force v → ~proof (later u) (later v)

  record _~_ {A} (x y : P A) : Set where
    coinductive
    field
      out~ : ~proof x y
open _~_

~→= : ∀{A} → (x y : P A) → x ~ y → x == y
~→= x y p = {!!}
