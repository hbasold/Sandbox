open import Data.Sum
open import Data.Fin
open import Data.Maybe
open import Signature

module MixedTest (Σ : Sig) (D : Set) where

-- Δ : Sig
-- Δ = record { ∥_∥ = D ; ar = λ x → Fin 1 }

mutual
  data Term : Set where
    cons : ⟪ Σ ⟫ (Term ⊎ CoTerm) → Term

  record CoTerm : Set where
    coinductive
    field destr : D → Maybe (Term ⊎ CoTerm)

open CoTerm public
