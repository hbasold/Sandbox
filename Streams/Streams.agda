{-# OPTIONS --copatterns --sized-types #-}

open import Size
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
open ≡-Reasoning

open import Data.List using (List; module List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; _×_; proj₁; proj₂)

-- Sized streams via head/tail.

record Stream {i : Size} (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : ∀ {j : Size< i} → Stream {j} A
open Stream public

-- Stream equality is bisimilarity
record _∼ˢ_ {A : Set} (s t : Stream A) : Set where
  coinductive
  field
    hd∼ : hd s ≡ hd t
    tl∼ : (tl s) ∼ˢ (tl t)
open _∼ˢ_ public

-- Functoriality.

map : ∀ {i A B} (f : A → B) (s : Stream {i} A) → Stream {i} B
hd (map     f s)     = f (hd s)
tl (map {i} f s) {j} = map {j} f (tl s {j})

-- Coalgebra structure
str-out : ∀{A} → Stream A → A × Stream A
str-out s = (hd s , tl s)

-- (weak) Finality
corec : ∀ {A X : Set} → (X → A × X) → (∀ {i} → X → Stream {i} A)
hd (corec f x) = proj₁ (f x)
tl (corec f x) = corec f (proj₂ (f x))

is-Bisim : ∀{A} → Rel (Stream A) _ → Set
is-Bisim R = ∀ x y → R x y → hd x ≡ hd y × R (tl x) (tl y)

ex-bisimulation→bisim : ∀{A R} → is-Bisim {A} R → ∀ {x y} → R x y → x ∼ˢ y
hd∼ (ex-bisimulation→bisim p {x} {y} xRy) = proj₁ (p x y xRy)
tl∼ (ex-bisimulation→bisim p {x} {y} xRy) =
  ex-bisimulation→bisim p (proj₂ (p x y xRy))

{-

-- Bisimulations
record Bisim {A X Y : Set}
  (c : X → A × X) (d : Y → A × Y) (x : X) (y : Y) : Set where
  coinductive
  field
    hdB : proj₁ (c x) ≡ proj₁ (d y)
    tlB : Bisim c d (proj₂ (c x)) (proj₂ (d y))
open Bisim public

-- The existence of a bisimulation between states in two coalgebras
-- implies that they are mapped to the same element in the final coalgebra.
ex-bisimulation→bisim : ∀{A X Y : Set}
  (c : X → A × X) (d : Y → A × Y) (x : X) (y : Y) →
  Bisim c d x y → (corec c x) ∼ˢ (corec d y)
hd∼ (ex-bisimulation→bisim c d x y p) = hdB p
tl∼ (ex-bisimulation→bisim c d x y p) =
  ex-bisimulation→bisim c d x' y' (tlB p)
  where
    x' = proj₂ (c x)
    y' = proj₂ (d y)
-}
