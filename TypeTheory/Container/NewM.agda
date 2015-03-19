{-# OPTIONS --copatterns --sized-types #-}

{- M types done properly coinductive -}
module NewM where

open import Size
open import Coinduction
open import Data.Product
open import Function
open import Data.M as M

record M' {i : Size} (A : Set) (B : A → Set) : Set where
  coinductive
  field
    d : ∀ {j : Size< i} → Σ A (λ x → (B x → M' {j} A B))
open M'

f : ∀{i} → {A : Set} {B : A → Set} → M A B → M' {i} A B
proj₁ (d (f x)) = head x
proj₂ (d (f x)) = f ∘ tail x

g : {A : Set} {B : A → Set} → M' A B → M A B
g x = inf (proj₁ (d x)) (λ b → ♯ g (proj₂ (d x) b))
