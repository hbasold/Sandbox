{-# OPTIONS --copatterns --sized-types #-}

module Streams where

open import Size
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
open ≡-Reasoning

open import Data.List using (List; module List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; _×_; proj₁; proj₂)

-- | Streams (with size annotations to ease definitions).
record Stream {i : Size} (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : ∀ {j : Size< i} → Stream {j} A
open Stream public

-- | Stream equality is bisimilarity
record _~_ {A : Set} (s t : Stream A) : Set where
  coinductive
  field
    hd~ : hd s ≡ hd t
    tl~ : (tl s) ~ (tl t)
open _~_ public

-- | Functoriality
map : ∀ {i A B} (f : A → B) (s : Stream {i} A) → Stream {i} B
hd (map     f s)     = f (hd s)
tl (map {i} f s) {j} = map {j} f (tl s {j})

-- | Coalgebra structure
str-out : ∀{A} → Stream A → A × Stream A
str-out s = (hd s , tl s)

-- | (Weak) Finality
corec : ∀ {A X : Set} → (X → A × X) → (∀ {i} → X → Stream {i} A)
hd (corec f x) = proj₁ (f x)
tl (corec f x) = corec f (proj₂ (f x))

-- | The usual definition of a bisimulation on streams.
Is-Bisim : ∀{A} → Rel (Stream A) _ → Set
Is-Bisim _R_ = ∀ x y → x R y → hd x ≡ hd y × (tl x) R (tl y)

-- | If R is a bisimulation then all elements related by R are bisimilar.
ex-bisimulation→bisim : ∀{A R} → Is-Bisim {A} R → ∀ {x y} → R x y → x ~ y
hd~ (ex-bisimulation→bisim p {x} {y} xRy) = proj₁ (p x y xRy)
tl~ (ex-bisimulation→bisim p {x} {y} xRy) =
  ex-bisimulation→bisim p (proj₂ (p x y xRy))

-- | Generalised bisimulations between arbitrary stream coalgebras.
Is-Bisim' : ∀{A X Y : Set} → (c : X → A × X) (d : Y → A × Y) → REL X Y _ → Set
Is-Bisim' c d _R_ = ∀ x y → x R y →
                  proj₁ (c x) ≡ proj₁ (d y) ×
                  (proj₂ (c x)) R (proj₂ (d y))

ex-bisimulation→bisim' : ∀{A X Y R c d} → Is-Bisim' {A} {X} {Y} c d R →
                         ∀ {x y} → R x y → corec c x ~ corec d y
hd~ (ex-bisimulation→bisim' p {x} {y} xRy) = proj₁ (p x y xRy)
tl~ (ex-bisimulation→bisim' p {x} {y} xRy) =
  ex-bisimulation→bisim' p (proj₂ (p x y xRy))
