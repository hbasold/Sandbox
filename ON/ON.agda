{-# OPTIONS --copatterns --sized-types #-}

open import Function
open import Data.Unit as Unit renaming (tt to ∗)
open import Data.List as List

TyCtx = List ⊤

data TyVar : (Γ : TyCtx) → Set where
  zero : ∀{Γ}                          → TyVar (∗ ∷ Γ)
  succ : ∀{Γ} → (x : TyVar Γ) → TyVar (∗ ∷ Γ)

data Type (Γ : TyCtx) : Set where
  unit :                                     Type Γ
  var  : (x : TyVar Γ)                     → Type Γ
  _⊕_  : (t₁ : Type Γ)       (t₂ : Type Γ) → Type Γ
  μ    : (t : Type (_ ∷ Γ))                → Type Γ
  _⊗_  : (t₁ : Type Γ)       (t₂ : Type Γ) → Type Γ
  _⇒_  : (t₁ : Type [])      (t₂ : Type Γ) → Type Γ
  ν    : (t : Type (_ ∷ Γ))                → Type Γ

-- | Variable renaming in types
_▹_ : (Γ Δ : TyCtx) → Set
Γ ▹ Δ = TyVar Γ → TyVar Δ

{-
rename : {Γ Δ : TyCtx} → (ρ : Γ ▹ Δ) → Type Γ → Type Δ
rename         ρ unit      = unit
rename         ρ (var x)   = var (ρ ∗ x)
rename         ρ (t₁ ⊕ t₂) = rename ρ t₁ ⊕ rename ρ t₂
rename {Γ} {Δ} ρ (μ t)     = μ (rename ρ' t)
  where
    ρ' : (∗ ∷ Γ) ▹ (∗ ∷ Δ)
    ρ' = ?
    -- ρ' = id {[ ∗ ]} ⧻ ρ
rename         ρ (t₁ ⊗ t₂) = rename ρ t₁ ⊗ rename ρ t₂
rename         ρ (t₁ ⇒ t₂) = t₁ ⇒ rename ρ t₂
rename {Γ} {Δ} ρ (ν t)     = ν (rename ρ' t)
  where
    ρ' : (∗ ∷ Γ) ▹ (∗ ∷ Δ)
    ρ' = ?
--    ρ' = ctx-id {[ ∗ ]} ⧻ ρ

-------------------------
---- Generating structure on contexts (derived from renaming)

weaken : {Γ : TyCtx} (Δ : TyCtx) → Type Γ -> Type (Δ ++ Γ)
weaken {Γ} Δ = rename {Γ} {Δ ++ Γ} ?

exchange : (Γ Δ : TyCtx) → Type (Γ ++ Δ) -> Type (Δ ++ Γ)
exchange Γ Δ = rename [ i₂ {Δ} {Γ} , i₁ {Δ} {Γ} ]

contract : {Γ : TyCtx} → Type (Γ ∐ Γ) -> Type Γ
contract = rename [ ctx-id , ctx-id ]

-}

Subst : TyCtx → TyCtx → Set
Subst Γ Δ = TyVar Γ → Type Δ

update : ∀{Γ Δ : TyCtx} → Subst Γ Δ → Type Δ → (Subst (∗ ∷ Γ) Δ)
update σ a zero        = a
update σ _ (succ x) = σ x


lift : ∀{Γ Δ} → Subst Γ Δ → Subst (∗ ∷ Γ) (∗ ∷ Δ)
lift σ zero = {!!}
lift σ (succ x) = {!!}

-- | Simultaneous substitution
subst : {Γ Δ : TyCtx} → (σ : Subst Γ Δ) → Type Γ → Type Δ
subst         σ unit      = unit
subst         σ (var x)   = σ x
subst         σ (t₁ ⊕ t₂) = subst σ t₁ ⊕ subst σ t₂
subst {Γ} {Δ} σ (μ t)     = μ (subst (lift σ) t)
subst         σ (t₁ ⊗ t₂) = subst σ t₁ ⊗ subst σ t₂
subst         σ (t₁ ⇒ t₂) = t₁ ⇒ subst σ t₂
subst {Γ} {Δ} σ (ν t)     = ν (subst (lift σ) t)


data Term : Set where
