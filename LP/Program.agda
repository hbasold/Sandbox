open import Signature

module Program (Σ : Sig) (V : Set) where

open import Function
open import Data.Empty
open import Data.Unit
open import Data.Product as Prod renaming (Σ to ⨿)
open import Data.Nat
open import Data.Fin
open import Data.List
open import Terms Σ

FinFam : Set → Set
FinFam X = ⨿ ℕ λ n → (Fin n → X)

dom : ∀{X} → FinFam X → Set
dom (n , _) = Fin n

get : ∀{X} (F : FinFam X) → dom F → X
get (_ , f) k = f k

domEmpty : ∀{X} → FinFam X → Set
domEmpty (zero  , _) = ⊤
domEmpty (suc _ , _) = ⊥

record Clause : Set where
  constructor _⊢_
  field
    body : FinFam (T V)
    head : T V
open Clause public

-- | A program consists of two finite sets of inductive and coinductive clauses.
Program : Set
Program = FinFam Clause × FinFam Clause

dom-μ : Program → Set
dom-μ = dom ∘ proj₁

dom-ν : Program → Set
dom-ν = dom ∘ proj₂

geth-μ : (P : Program) → dom-μ P → T V
geth-μ P = head ∘ get (proj₁ P)

getb-μ : (P : Program) → dom-μ P → FinFam (T V)
getb-μ P = body ∘ get (proj₁ P)

geth-ν : (P : Program) → dom-ν P → T V
geth-ν P = head ∘ get (proj₂ P)

getb-ν : (P : Program) → dom-ν P → FinFam (T V)
getb-ν P = body ∘ get (proj₂ P)
