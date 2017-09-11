module StreamPredicates where

open import PropsAsTypes
open import Stream

module Modalities (A : Set) where

  private
    Aω : Set
    Aω = Stream A

  record Always (P : Pred Aω) (s : Stream A) : Prop where
    coinductive
    field
      valid : P s
      step : Always P (tl s)
  open Always public

  data Eventually (P : Pred Aω) (s : Stream A) : Prop where
    now : P s → Eventually P s
    later : Eventually P (tl s) → Eventually P s

  GE : Pred Aω → Pred Aω
  GE P = Always (Eventually P)

  EG : Pred Aω → Pred Aω
  EG P = Eventually (Always P)

  Always⇒GE : ∀{P : Pred Aω} → Always P ⊆ GE P
  Always⇒GE s p .valid = now (p .valid)
  Always⇒GE s p .step  = Always⇒GE (s .tl) (p .step)

  EG⇒Eventually : ∀{P : Pred Aω} → EG P ⊆ Eventually P
  EG⇒Eventually s (now p)      = now (p .valid)
  EG⇒Eventually s (later Evs') = later (EG⇒Eventually (s .tl) Evs')

  EG⇒GE : ∀{P : Pred Aω} → EG P ⊆ GE P
  EG⇒GE s p         .valid = EG⇒Eventually s p
  EG⇒GE s (now p)   .step  = Always⇒GE (tl s) (p .step)
  EG⇒GE s (later p) .step  = EG⇒GE (tl s) p

module ModalitiesExamples where
  open import Data.Nat
  open import Relation.Binary.PropositionalEquality as PE

  exP : Pred (Stream ℕ)
  exP s = s .hd ≡ 0

  alt : Stream ℕ
  alt .hd     = 0
  alt .tl .hd = 1
  alt .tl .tl = alt

  open Modalities ℕ

  exP-holds-on-alt-GE : GE exP alt
  exP-holds-on-alt-GE .valid       = now refl
  exP-holds-on-alt-GE .step .valid = later (now refl)
  exP-holds-on-alt-GE .step .step  = exP-holds-on-alt-GE

  exP-holds-not-on-alt-EG : ¬ (EG exP alt)
  exP-holds-not-on-alt-EG (now p)         = zero-not-suc 0 (p .step .valid)
  exP-holds-not-on-alt-EG (later (now p)) = zero-not-suc 0 (p .valid)
  exP-holds-not-on-alt-EG (later (later EGalt'')) =
    exP-holds-not-on-alt-EG EGalt''
