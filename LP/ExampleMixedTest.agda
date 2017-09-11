open import Data.Sum
open import Data.Fin
open import Data.Product
open import Data.Maybe
open import Signature

Σ-N∞ : Sig
Σ-N∞ = record { ∥_∥ = Fin 2 ; ar = Σ-N∞-ar }
  where
    Σ-N∞-ar : Fin 2 → Set
    Σ-N∞-ar zero    = Fin 0
    Σ-N∞-ar (suc zero) = Fin 1
    Σ-N∞-ar (suc (suc ()))

D-N∞ : Set
D-N∞ = Fin 1

open import MixedTest Σ-N∞ D-N∞ as LP-N∞ renaming (Term to N∞μ; CoTerm to N∞)

stop' : N∞μ
stop' = cons (# 0 , λ())

step' : N∞ → N∞μ
step' x = (cons (# 1 , (λ _ → inj₂ x)))

-- Immediate stop -> 0
stop : N∞
destr stop zero = just (inj₁ stop')
destr stop (suc ())

-- Do a step -> successor
succ : N∞ → N∞
destr (succ x) zero    = just (inj₁ (step' x))
destr (succ x) (suc ())

-- Not actually in N∞
foo : N∞
destr foo x = nothing
