module FairStream where


open import Level as Level using (zero)
open import Size
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
open ≡-Reasoning

-- open import Data.List using (List; module List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product renaming (map to pmap)

open import Stream

data List⁺ (A : Set) : Set where
  one : A → List⁺ A
  _∷_ : A → List⁺ A → List⁺ A

mutual
  data LFin (A B : Set) : Set where
    lin : A × LFin A B → LFin A B
    rinl : RFin A B → LFin A B

  data RFin (A B : Set) : Set where
    rin : B × RFin A B → RFin A B
    linr : LFin A B → RFin A B

Fair Fair' : Set → Set → Set

Fair A B = Stream (LFin A B)

Fair' A B = Stream (List⁺ A × List⁺ B)

α : ∀{A B} → Fair A B → Fair' A B
hd (α {A} {B} u) = (f₁ (hd u) , g (hd u))
  where
    f₁ : LFin A B → List⁺ A
    f₂ : RFin A B → List⁺ A

    f₁ (lin (a , x)) = a ∷ f₁ x
    f₁ (rinl x) = f₂ x

    f₂ (rin (b , y)) = f₂ y
    f₂ (linr x) = f₁ x

    g : LFin A B → List⁺ B
    g (lin x) = {![]!}
    g (rinl x) = {!!}
tl (α u) = {!!}
