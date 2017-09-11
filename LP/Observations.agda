open import Signature
import Program

module Observations (Σ : Sig) (V : Set) (P : Program.Program Σ V) where

open import Terms Σ
open import Program Σ V
open import Rewrite Σ V P
open import Function
open import Relation.Nullary
open import Relation.Unary
open import Data.Product as Prod renaming (Σ to ⨿)
open import Streams hiding (_↓_)

-- | We will need _properly refining_ substitutions: σ properly refines t ∈ T V,
-- if ∀ v ∈ fv(t). σ(v) = f(α) for f ∈ Σ.
-- Then an observation step must go along a properly refining substitution,
-- which in turn allows us to construct a converging sequence of terms.

{- |
We can make an observation according to the following rule.

t ↓ s   fv(s) ≠ ∅    ∃ k, σ. s ~[σ]~ Pₕ(k)
--------------------------------------------
              t ----> t[σ]
-}
data _↦_ (t : T V) : T V → Set where
  obs-step : {s : T V} → t ↓ s → -- ¬ Empty (fv s) →
             (cl : dom P) {σ : Subst V V} →
             ProperlyRefining t σ → mgu s (geth P cl) σ →
             t ↦ app σ t

reduct : ∀{t s} → t ↦ s → T V
reduct (obs-step {s} _ _ _ _ ) = s

refining : ∀{t s} → t ↦ s → Subst V V
refining (obs-step _ _ {σ} _ _) = σ

is-refining : ∀{t s} (o : t ↦ s) → ProperlyRefining t (refining o)
is-refining (obs-step _ _ r _) = r

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
open CoindDerivable public

obs-result : ∀{t} → CoindDerivable t → T V
obs-result = proj₁ ∘ der-obs

get-obs : ∀{t} (d : CoindDerivable t) → t ↦ (obs-result d)
get-obs = proj₁ ∘ proj₂ ∘ der-obs

-- | This should give us convergence to a term in T∞ V, see Terms.agda
coind-deriv-seq : (t : T V) → CoindDerivable t → ProperlyRefiningSeq t
hd-ref (coind-deriv-seq t d) = refining (get-obs d)
hd-is-ref (coind-deriv-seq t d) = is-refining (get-obs d)
tl-ref (coind-deriv-seq t d) with (der-obs d)
tl-ref (coind-deriv-seq t d) | ._ , obs-step red cl {σ} ref _ , d' =
  coind-deriv-seq (app σ t) d'
