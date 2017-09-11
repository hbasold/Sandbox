open import Signature
import Program

-- | Herbrand model that takes the distinction between inductive
-- and coinductive clauses into account.
module Herbrand (Σ : Sig) (V : Set) (P : Program.Program Σ V) where

open import Function
open import Data.Empty
open import Data.Product as Prod renaming (Σ to ⨿)
open import Data.Sum as Sum
open import Relation.Unary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Program Σ V
open import Terms Σ

mutual
  record Herbrand-ν (t : T∞ ⊥) : Set where
    coinductive
    field
      bw-closed :
        (∀ (i : dom-ν P) {σ} →
           (t ~ app∞ σ (χ (geth-ν P i))) →
           ∀ (j : dom (getb-ν P i)) →
           (app∞ σ (χ (get (getb-ν P i) j))) ∈ Herbrand-ν)
        ⊎ (t ∈ Herbrand-μ)

  data Herbrand-μ : T∞ ⊥ → Set where
    fw-closed : (t : T∞ ⊥) → (t ∈ Herbrand-μ) → (i : dom-μ P) (σ : Subst∞ V ⊥) →
                t ≡ app∞ σ (χ (geth-μ P i)) → (j : dom (getb-μ P i)) →
                Herbrand-μ (app∞ σ (χ (get (getb-μ P i) j)))
    coind-μ : {t : T∞ ⊥} → t ∈ Herbrand-ν → Herbrand-μ t

open Herbrand-ν public
