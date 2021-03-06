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
    force : S
open D

-- | Action of D on morphisms
D₁ : ∀ {X Y} → (X → Y) → D X → D Y
force (D₁ f x) = f (force x)

-- | D lifted to dependent functions
↑D₁ : ∀ {A} → (B : A → Set) → ((x : A) → B x) → (y : D A) → D (B (force y))
force (↑D₁ B f y) = f (force y)

D-intro : ∀ {H : Set → Set} → (∀ {X} → H X → X) → (∀ {X} → H X → D X)
force (D-intro f x) = f x

D-intro2 : ∀ {X S : Set} → (X → S) → X → D S
force (D-intro2 f x) = f x

postulate
  -- | We'll need coinduction to prove such equalities in the future, or prove
  -- it from univalence.
  D-coind : ∀ {S} {x y : D S} → force x == force y → x == y

D-coind2 : ∀ {S} {x y : D S} → D (force x == force y) → x == y
D-coind2 p = D-coind (force p)

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

  P-out : ∀ {A} → P A → A ⊔ ∞P A
  P-out (#p (#now a) _)   = inl a
  P-out (#p (#later x) _) = inr x

  ∞P-intro : ∀ {A X : Set} → (X → A ⊔ X) → (X → ∞P A)
  ∞P-intro {A} {X} f = ∞P-intro'
--    match (f x) withl D-intro2 now withr (D-intro2 (later ∘ ∞P-intro'))
    where
      ∞P-intro' : X → ∞P A
      force (∞P-intro' x) =
        match (f x) withl now withr (λ x' → later (∞P-intro' x'))

  postulate  -- HIT
    weak~ : ∀{A} → (x : ∞P A) → (later x == force x)

  -- | Extra module for recursion using sized types.
  -- This is convenient, as we can use the functor D in the definition, which
  -- in turn simplifies proofs.
  module PRec {A} {X : Set}
    (now* : A → X)
    (later* : D X → X)
    (weak~* : (x : D X) → (later* x == force x))
    where
      f : ∀ {i} → P {i} A → X
      f = f-aux phantom where
        f-aux : ∀ {i} → Phantom weak~* → #P {i} A → X
        f-aux phantom (#p (#now a) _)        = now* a
        f-aux phantom (#p (#later {j} x') _) = later* (D₁ (f {j}) x')

      postulate      -- HIT
        weak~-β : (x : ∞P A) → ap f (weak~ x) == weak~* (D₁ f x)

  module PElim {A} {S : P A → Set}
    (now* : ∀(a : A) → S (now a))
    (later* : (x : ∞P A) → (x_rec : D (S (force x))) → S (later x))
    (weak~* : (x : ∞P A) → (x_rec : D (S (force x))) →
              (later* x x_rec == (force x_rec) [ S ↓ (weak~ x) ]))
    where
      g-aux : Phantom weak~* → (y : ∞P A) → D (S (force y))

      f-aux : Phantom weak~* → (x : P A) → S x
      f-aux phantom (#p (#now a) _)    = now* a
      f-aux phantom (#p (#later x') _)
        = later* x' (g-aux phantom x') -- (↑D₁ S f x')

      force (g-aux phantom y) = f-aux phantom (force y)

      g : (y : ∞P A) → D (S (force y))
      g = g-aux phantom

      f : (x : P A) → S x
      f = f-aux phantom

      g-is-D₁f : (y : ∞P A) → g y == ↑D₁ S f y
      g-is-D₁f y = D-coind lem
        where
          lem : force (g y) == force (↑D₁ S f y)
          lem =
            force (g y)
              =⟨ idp ⟩
            f (force y)
              =⟨ idp ⟩
            force (↑D₁ S f y)
            ∎

      f-homomorphism : (y : ∞P A) → f (later y) == later* y (↑D₁ S f y)
      f-homomorphism y =
          f (later y)
        =⟨ idp ⟩
          later* y (g y)
        =⟨ g-is-D₁f y |in-ctx later* y ⟩
          later* y (↑D₁ S f y)
        ∎

      postulate      -- HIT
        weak~-β : (x : ∞P A) → apd f (weak~ x) == weak~* x (g x)

{-
      weak~-β₂ : (x : ∞P A) →
                 apd f (weak~ x) == weak~* x (↑D₁ S f x)
                  -- transport (weak~* x) g-is-D₁f (↑D₁ S f x)
      weak~-β₂ = ?
-}

open PRec public renaming (f to P-rec)
open PElim public
  renaming (f to P-elim; g to ∞P-elim; f-homomorphism to P-elim-hom;
           weak~-β to elim-weak~-β)

module Bla where

-- | Copairing of morphisms
[_,_] : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  (l : A → C) (r : B → C) → (x : Coprod A B) → C
[ f , g ] x = match x withl f withr g

-- | Inverse of [now, later] à la Lambek,
-- given by extending id + D ([now, later]) : A ⊔ D(A ⊔ ∞P A) → A ⊔ ∞P A.
out : ∀ {A} → P A → A ⊔ ∞P A
out {A} = P-rec inl force (λ _ → idp)
    -- (inr ∘ D₁ [ now , later ]) resp-weak~
    where
      resp-weak~ : (x : D (A ⊔ ∞P A)) →
                   (inr ∘ D₁ [ now , later ]) x == force x
      resp-weak~ x =
        (inr ∘ D₁ [ now , later ]) x
          =⟨ {!!} ⟩
        inr (D₁ [ now , later ] x)
          =⟨ {!!} ⟩
        force x
          ∎


⊥' : ∀ {A} → ∞P A

⊥ : ∀ {A} → P A
⊥ = later (D-intro (λ _ → {!!}) unit)

force ⊥' = {!!} -- ⊥

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

    =-later : (x : ∞P (P A)) → D (T (force x)) → T (later x)
    =-later x p = transport T (! (weak~ x)) (force p)

    r : (x : ∞P (P A)) → (p : D (T (force x))) →
        (=-later x p) == (force p) [ T ↓ (weak~ x) ]
    r x p = trans-↓ T (weak~ x) (force p)

    q : (x : P (P A)) → μ ( P₁ (P₁ f) x) == P₁ f (μ x)
    q = P-elim {S = λ x → μ ( P₁ (P₁ f) x) == P₁ f (μ x)}
        (λ a → idp) =-later r

-- | Termination predicate on P A
data _↓_ {A} (x : P A) : A → Set where
  now↓ : (a : A) → now a == x → x ↓ a
  later↓ : (a : A) → (u : ∞P A) → (later u == x) → (force u) ↓ a → x ↓ a

mutual
  -- | Weak bisimilarity proofs
  data ~proof {A} (x y : P A) : Set where
    terminating : (a : A) → x ↓ a → y ↓ a → ~proof x y
    -- A bit awkward, but otherwise we cannot pattern matching on ~proof
    step : (u v : ∞P A) → (later u == x) → (later v == y) → force u ~ force v →
           ~proof x y

  -- | Weak bisimilarity for P A
  record _~_ {A} (x y : P A) : Set where
    coinductive
    field
      out~ : ~proof x y
open _~_

terminate→=now : ∀{A} → (a : A) → (x : P A) → x ↓ a → now a == x
terminate→=now a x (now↓ .a na=x) = na=x
terminate→=now a x (later↓ .a u lu=x fu↓a) =
  now a
    =⟨ terminate→=now a (force u) fu↓a ⟩
  force u
    =⟨ ! (weak~ u) ⟩
  later u
    =⟨ lu=x ⟩
  x
    ∎

lemma : ∀{A} → (a : A) → (x y : P A) → x ↓ a → y ↓ a → x == y
lemma a x y x↓a y↓a =
  x
    =⟨ ! (terminate→=now a x x↓a) ⟩
  now a
    =⟨ terminate→=now a y y↓a ⟩
  y
    ∎

inr-inj : ∀ {i} {A B : Set i} →
          (x y : B) → Path {i} {A ⊔ B} (inr x) (inr y) → x == y
inr-inj x .x idp = idp

later-inj : ∀ {A} → (u v : ∞P A) → later u == later v → u == v
later-inj u v p = inr-inj u v lem
  where
    lem : inr u == inr v
    lem = transport (λ z → inr u == P-out z) {later u} {later v} p idp

-- | Weak bisimilarity implies equality for P A
~→= : ∀{A} → (x y : P A) → x ~ y → x == y
~→= {A} x y = P-elim {S = λ x' → x' ~ y → x' == y} now-= later-= weak~-= x
  where
    now-= : (a : A) → now a ~ y → now a == y
    now-= a p = lem (out~ p)
      where
        lem : ~proof (now a) y → now a == y
        lem (terminating b (now↓ .b nb=na) y↓b) =
          now a
            =⟨ ! nb=na ⟩
          now b
            =⟨ terminate→=now b y y↓b ⟩
          y
            ∎
        lem (terminating b (later↓ .b u () now_a↓b) y↓b)
        lem (step u v () x₂ x₃)

    later-= : (u : ∞P A) →
              D (force u ~ y → force u == y) → later u ~ y → later u == y
    later-= u p later_u~y = lem (out~ later_u~y)
      where
        lem : ~proof (later u) y → later u == y
        lem (terminating a later_u↓a y↓a) = lemma a (later u) y later_u↓a y↓a
        lem (step u' v later_u'=later_u later_v=y force_u'~force_v) =
          later u
            =⟨ weak~ u ⟩
          force u
            =⟨ force p force_u~y ⟩
          y ∎
          where
            force_u'=force_u : force u' == force u
            force_u'=force_u =
              force u'
                =⟨ later-inj u' u later_u'=later_u |in-ctx force ⟩
              force u
                ∎

            y=force_v : y == force v
            y=force_v =
              y
                =⟨ ! later_v=y ⟩
              later v
                =⟨ weak~ v ⟩
              force v
                ∎

            force_u~y : force u ~ y
            force_u~y = transport
                   (λ z → z ~ y)
                   force_u'=force_u
                   (transport! (λ z → force u' ~ z) y=force_v force_u'~force_v)

    weak~-= : (u : ∞P A) (p : D (force u ~ y → force u == y)) →
              (later-= u p)
                == (force p) [ (λ x' → x' ~ y → x' == y) ↓ (weak~ u) ]
    weak~-= u p = {!!}
