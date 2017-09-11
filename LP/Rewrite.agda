open import Signature
import Program

module Rewrite (Σ : Sig) (V : Set) (P : Program.Program Σ V) where

open import Terms Σ
open import Program Σ V
open import Data.Empty renaming (⊥ to ∅)
open import Data.Unit
open import Data.Product as Prod renaming (Σ to ⨿)
open import Data.Sum as Sum
open import Data.Fin
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

data _⟿_ (t : T V) : T V → Set where
  rew-step : (cl : dom P) (i : dom (getb P cl)) {σ : Subst V V} →
             matches (geth P cl) t σ → -- (mgm t (geth P cl) σ) →
             t ⟿ app σ (get (getb P cl) i)

Val : Pred (T V) _
Val t = (cl : dom P) (i : dom (getb P cl)) {σ : Subst V V} →
        ¬ (matches (geth P cl) t σ)

no-rewrite-on-vals : (t : T V) → Val t → (s : T V) → ¬ (t ⟿ s)
no-rewrite-on-vals t p ._ (rew-step cl i q) = p cl i q

data _↓_ (t : T V) : T V → Set where
  val : Val t → t ↓ t
  step : (r s : T V) → r ↓ s → t ⟿ r → t ↓ s

{- Strongly normalising terms wrt to P are either in normal form, i.e. values,
or for every clause that matches, every rewrite step must be SN.
This is an adaption of the usual (constructive) definition.
-}
data SN (t : T V) : Set where
  val-sn   : Val t → SN t
  steps-sn : (cl : dom P) (i : dom (getb P cl)) {σ : Subst V V} →
             (matches t (geth P cl) σ) →
             SN (app σ (get (getb P cl) i)) →
             SN t

-- | Determines whether a term t is derivable from an axiom, i.e., whether
-- there is a clause " ⇒ p" such that p matches t.
Axiom : Pred (T V) _
Axiom t = ∃₂ λ cl σ → (mgm t (geth P cl) σ) × (domEmpty (getb P cl))

-- | An inductively valid term is derivable in finitely many steps from
-- axioms.
data Valid (t : T V) : Set where
  val-sn   : Axiom t → Valid t
  steps-sn : (cl : dom P) (i : dom (getb P cl)) {σ : Subst V V} →
             (matches t (geth P cl) σ) →
             Valid (app σ (get (getb P cl) i)) →
             Valid t



{-


⊥ : {X : Set} → X ⊎ ⊤
⊥ = inj₂ tt

record Rew-Branch (F : T V → Set) (t : T V) : Set where
  constructor prf-branch
  field
    clause : dom P
    matcher : Subst V V
    isMgm : mgm t (geth P clause) matcher
    next : (i : dom (getb P clause)) →
           F (app matcher (get (getb P clause) i))

-- | Set of rewrite trees starting in t that use the rules given in P.
-- If the tree is ⊥, then t cannot be rewritten by any of the rules of P.
data Rew (t : T V) : Set where
  in-prf : Rew-Branch Rew t ⊎ ⊤ → Rew t

-- | Just as Rew, only that we also allow infinite rewriting sequences.
record Rew∞ (t : T V) : Set where
  coinductive
  field out-prf : Rew-Branch Rew∞ t ⊎ ⊤
open Rew∞

out-prf⁻¹ : ∀{t} → Rew-Branch Rew∞ t ⊎ ⊤ → Rew∞ t
out-prf (out-prf⁻¹ b) = b

-- | Finite rewriting trees are included in the set of the possibly infinite
-- ones.
χ-prf : ∀{t} → Rew t → Rew∞ t
χ-prf (in-prf (inj₁ (prf-branch c m isMgm next))) =
  out-prf⁻¹ (inj₁ (prf-branch c m isMgm (λ i → χ-prf (next i))))
χ-prf (in-prf (inj₂ tt)) = out-prf⁻¹ ⊥

Rew-Step : (F : {s : T V} → Rew∞ s → Set) → {t : T V} (R : Rew∞ t) → Set
Rew-Step F R with out-prf R
Rew-Step F R | inj₁ (prf-branch clause matcher isMgm next) = {!!}
Rew-Step F R | inj₂ tt = ∅

data Path {t : T V} (R : Rew∞ t) : Set where
  root : Path R
  step : {!!} → Path R
-}
