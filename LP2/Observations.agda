open import Signature
import Program

module Observations (Σ : Sig) (V : Set) (P : Program.Program Σ V) where

open import Terms Σ
open import Program Σ V
open import Rewrite Σ V P
open import Relation.Nullary
open import Relation.Unary
open import Data.Product as Prod renaming (Σ to ⨿)

NonTrivial : T V → Pred (Subst V V) _
NonTrivial t σ = ∃ λ v → (v ∈ fv t) × ¬ isVar (σ v)

{- |
We can make an observation according to the following rule.

t ↓ s   fv(s) ≠ ∅    ∃ k, σ. s ~[σ]~ Pₕ(k)
--------------------------------------------
              t ----> t[σ]
-}
data _↦_ (t : T V) : T V → Set where
  obs-step : {s : T V} → t ↓ s → ¬ Empty (fv s) →
             (cl : dom P) {σ : Subst V V} → mgu s (geth P cl) σ →
             t ↦ app σ t

GroundTerm : Pred (T V) _
GroundTerm t = Empty (fv t)

--------
-- FLAW: This does not allow us to distinguish between inductive
-- and coinductive definitions on the clause level.
-- The following definitions are _global_ for a derivation!
-------

data IndDerivable (t : T V) : Set where
  ground : GroundTerm t → Valid t → IndDerivable t
  der-step : (s : T V) → t ↦ s → IndDerivable s → IndDerivable t

record CoindDerivable (t : T V) : Set where
  coinductive
  field
    term-SN : SN t
    der-obs : ⨿ (T V) λ s → t ↦ s × CoindDerivable s
open CoindDerivable

record _↥[_]_ (t : T V) (σ : Subst∞ V V) (s : T∞ V) : Set where
  coinductive
  field
    conv-match : app∞ σ (χ t) ~ s
    conv-step : ⨿ (T V) λ t₁ → t ↦ t₁ × t₁ ↥[ ? ] s

coind-converges-to : (t : T V) → CoindDerivable t → T∞ V
out (coind-converges-to t p) with der-obs p
... | (._ , obs-step t↓s _ cl {σ} _ , q) = {!!}

coind-converges : (t : T V) → CoindDerivable t →
                  ∃₂ λ s σ → Empty (fv∞ s) × t ↥[ σ ] s
coind-converges = {!!}
