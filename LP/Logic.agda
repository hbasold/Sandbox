open import Signature

-- | One signature for terms and one for predicates.
module Logic (Σ Δ : Sig) (V : Set) where

open import Data.Empty renaming (⊥ to Ø)
open import Data.Unit
open import Data.Sum
open import Data.Product renaming (Σ to ∐)
open import Data.Nat
open import Data.Fin

FinSet : Set → Set
FinSet X = ∃ λ n → (Fin n → X)

dom : ∀{X} → FinSet X → Set
dom (n , _) = Fin n

get : ∀{X} (F : FinSet X) → dom F → X
get (_ , f) k = f k

drop : ∀{X} (F : FinSet 

domEmpty : ∀{X} → FinSet X → Set
domEmpty (zero  , _) = ⊤
domEmpty (suc _ , _) = Ø


open import Terms Σ

Term : Set
Term = T V

-- | An atom is either a predicate on terms or bottom.
Atom : Set
Atom = ⟪ Δ ⟫ Term -- ⊎ ⊤

{-
⊥ : Atom
⊥ = inj₂ tt
-}

Formula : Set
Formula = Atom

Sentence : Set
Sentence = FinSet Formula

data Parity : Set where
  ind : Parity
  coind : Parity

record Clause : Set where
  constructor _⊢[_]_
  field
    head : Sentence
    par : Parity
    concl : Formula
open Clause public

Program : Set
Program = FinSet Clause

indClauses : Program → Program
indClauses (zero , P) = zero , λ ()
indClauses (suc n , P) = {!!}
