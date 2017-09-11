module Syntax where

import Level
open import Data.Unit as Unit renaming (tt to ∗)
open import Data.List as List
open import Data.Product
open import Categories.Category using (Category)
open import Function

open import Relation.Binary.PropositionalEquality as PE hiding ([_]; subst)
open import Relation.Binary using (module IsEquivalence; Setoid; module Setoid)
open ≡-Reasoning

open import Common.Context as Context

Univ = ⊤

data FP : Set where
  μ : FP
  ν : FP

mutual
  TypeCtx : Set
  TypeCtx = Ctx (TermCtx × Univ)

  data Type : TypeCtx → TermCtx → TermCtx → Univ → Set

  data TermCtx : Set where
    Ø : TermCtx
    _∷'_ : {i : Univ} → (Γ : TermCtx) → Type [] Γ Ø i → TermCtx

  data Term (Γ Γ' : TermCtx) {i : Univ} :
            Type [] Γ Γ' i → Type [] Γ Γ' i → Set

  TypeVar : TypeCtx → TermCtx → Univ → Set
  TypeVar Δ Γ i = Var Δ (Γ , i)

  data CtxMor (Γ : TermCtx) : TermCtx → Set where
    ⟨⟩ : CtxMor Γ Ø
    _⋉_ : {i : Univ} {Γ' : TermCtx} {A : Type [] Γ' Ø i}
          (f : CtxMor Γ Γ') → Term Γ (subst A f) → CtxMor Γ (Γ ∷' A)

  reidx : {Δ : TypeCtx} {Γ Γ' : TermCtx} {i : Univ} →
          CtxMor Γ' Γ → Type Δ Γ Ø i → Type Δ Γ' Ø i
  reidx = ?

  data Term (Γ Γ' : TermCtx) {i : Univ} :
            Type [] Γ Γ' i → Type [] Γ Γ' i → Set where
       in₁ : {i : Univ} {X : TypeVar [(Γ , i)] Γ i}
             {Γ₁ : TermCtx} (A₁ : Type [(Γ , i)] Γ₁ Ø i) (f₁ : Γ₁ ▹ Γ) →
             Term Γ Γ' i (tySubst (fp A₁ f₁ μ) A₁ X) (reidx f₁ (fp A₁ f₁ μ))

  {-
  _++'_ : TermCtx → TermCtx → TermCtx
  Γ₁ ++' Ø         = Γ₁
  Γ₁ ++' (Γ₂ ∷' A) = 
-}
  data Type : TypeCtx → TermCtx → TermCtx → Univ → Set where
    tyVar : (Δ : TypeCtx) → (Γ : TermCtx) → (i : Univ) → Type Δ Ø Γ i
--    app :
    fp : {Δ : TypeCtx} {Γ : TermCtx} {i : Univ} {X : TypeVar Δ Γ i}
         {Γ₁ : TermCtx} (A₁ : Type Δ Γ₁ Ø i)
         (f₁ : Γ₁ ▹ Γ)
         (ρ : FP) →
         Type Δ Ø Γ i
{-    fp : {Δ : TypeCtx} {X : TypeVar} {Γ Γ' Γ₁ : TermCtx} {i : Univ}
         (A₁ : Type Δ (Γ' ++' Γ₁)
-}
