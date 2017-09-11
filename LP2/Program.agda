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
open Clause

Program : Set
Program = FinFam Clause

geth : (P : Program) → dom P → T V
geth P = head ∘ get P

getb : (P : Program) → dom P → FinFam (T V)
getb P = body ∘ get P
