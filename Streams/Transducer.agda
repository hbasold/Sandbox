module Transducer where

open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.List

_* = List

-- | Finite and infinite sequences (constructively useful variant)
record Seq (A : Set) : Set where
  coinductive
  field
    out : (A ⊎ ⊤) × Seq A
open Seq

-- | Functor that allows us to capture transducer as coalgebras.
F : (A B : Set) → Set → Set
F A B X = A → B * × X

-- | Interpretation of transducers as maps between sequences, i.e., corecursion.
⟦_⟧ : ∀{A B X} → (δ : X → F A B X) → X → (Seq A → Seq B)
out (⟦_⟧ {B = B} {X} δ x s) with out s
... | (inj₁ a , t) =
  let (w , y) = δ x a
  in cont y w
  where
    cont : X → B * → (B ⊎ ⊤) × Seq B
    cont y [] = (inj₂ tt , ⟦ δ ⟧ y t)
    proj₁ (cont y (b ∷ bs)) = inj₁ b
    out (proj₂ (cont y (b ∷ bs))) = cont y bs
... | (inj₂ tt , y) = (inj₂ tt , ⟦ δ ⟧ x y)
