module Types where

import Level
open import Data.Unit as Unit renaming (tt to ∗)
open import Data.List as List
open import Categories.Category using (Category)
open import Function

open import Relation.Binary.PropositionalEquality as PE hiding ([_]; subst)
open import Relation.Binary using (module IsEquivalence; Setoid; module Setoid)
open ≡-Reasoning

Kind = ⊤
import Common.Context Kind as Context
open import Common.Context Kind
  using (Ctx; Var; zero; ctx-cat; ctx-bin-coproducts; _≅V_; ≅V-setoid; Vrefl; Vsym; Vtrans)
  renaming (succ to succ′)
open import Categories.Object.BinaryCoproducts ctx-cat
open BinaryCoproducts ctx-bin-coproducts

postulate
  η-≡ : {A : Set} {B : A → Set}
         {f₁ : (x : A) → B x}{f₂ : (y : A) → B y} →
         ((x : A) → f₁ x ≡ f₂ x) → f₁ ≡ f₂

TyCtx = Ctx
TyVar : Ctx → Set
TyVar Γ = Var Γ ∗
succ : ∀{Γ} (x : TyVar Γ) → TyVar (∗ ∷ Γ)
succ = Context.succ ∗

open Categories.Category.Category ctx-cat
  renaming ( _⇒_ to _▹_
           ; _≡_ to _≈_
           ; _∘_ to _●_
           ; id  to ctx-id
           )

-- | Type syntax
data Type (Γ : TyCtx) : Set where
  unit :                                     Type Γ
  var  : (x : TyVar Γ)                     → Type Γ
  _⊕_  : (t₁ : Type Γ)       (t₂ : Type Γ) → Type Γ
  μ    : (t : Type (_ ∷ Γ))                → Type Γ
  _⊗_  : (t₁ : Type Γ)       (t₂ : Type Γ) → Type Γ
  _⇒_  : (t₁ : Type [])      (t₂ : Type Γ) → Type Γ
  ν    : (t : Type (_ ∷ Γ))                → Type Γ

-- | Congruence for types
data _≅T_  {Γ Γ' : Ctx} : Type Γ → Type Γ' → Set where
  unit : unit ≅T unit
  var  : ∀{x : TyVar Γ} {x' : TyVar Γ'} → (x ≅V x') → var x ≅T var x'
  _⊕_  : ∀{t₁ t₂ : Type Γ} {t₁' t₂' : Type Γ'} →
         (t₁ ≅T t₁') → (t₂ ≅T t₂') →
         (t₁ ⊕ t₂) ≅T (t₁' ⊕ t₂')
  _⊗_  : ∀{t₁ t₂ : Type Γ} {t₁' t₂' : Type Γ'} →
         (t₁ ≅T t₁') → (t₂ ≅T t₂') →
         (t₁ ⊗ t₂) ≅T (t₁' ⊗ t₂')
  μ    : ∀{t : Type (∗ ∷ Γ)} {t' : Type (∗ ∷ Γ')} →
         (t ≅T t') →
         (μ t) ≅T (μ t')
  _⇒_  : ∀{t₁ t₁' : Type []} {t₂ : Type Γ} {t₂' : Type Γ'} →
         (t₁ ≅T t₁') → (t₂ ≅T t₂') →
         (t₁ ⇒ t₂) ≅T (t₁' ⇒ t₂')
  ν    : ∀{t : Type (∗ ∷ Γ)} {t' : Type (∗ ∷ Γ')} →
         (t ≅T t') →
         (ν t) ≅T (ν t')

Trefl : ∀ {Γ : Ctx} {t : Type Γ} → t ≅T t
Trefl {t = unit}    = unit
Trefl {t = var x}   = var e.refl
  where
    module s = Setoid
    module e = IsEquivalence (s.isEquivalence ≅V-setoid)
Trefl {t = t₁ ⊕ t₂} = Trefl ⊕ Trefl
Trefl {t = μ t}     = μ Trefl
Trefl {t = t ⊗ t₁}  = Trefl ⊗ Trefl
Trefl {t = t ⇒ t₁}  = Trefl ⇒ Trefl
Trefl {t = ν t}     = ν Trefl

Tsym : ∀ {Γ Γ' : Ctx} {t : Type Γ} {t' : Type Γ'} → t ≅T t' → t' ≅T t
Tsym unit      = unit
Tsym (var u)   = var (Vsym u)
Tsym (u₁ ⊕ u₂) = Tsym u₁ ⊕ Tsym u₂
Tsym (u₁ ⊗ u₂) = Tsym u₁ ⊗ Tsym u₂
Tsym (μ u)     = μ (Tsym u)
Tsym (u₁ ⇒ u₂) = Tsym u₁ ⇒ Tsym u₂
Tsym (ν u)     = ν (Tsym u)

Ttrans : ∀ {Γ₁ Γ₂ Γ₃ : Ctx} {t₁ : Type Γ₁} {t₂ : Type Γ₂} {t₃ : Type Γ₃} →
         t₁ ≅T t₂ → t₂ ≅T t₃ → t₁ ≅T t₃
Ttrans unit unit           = unit
Ttrans (var u₁) (var u₂)   = var (Vtrans u₁ u₂)
Ttrans (u₁ ⊕ u₂) (u₃ ⊕ u₄) = Ttrans u₁ u₃ ⊕ Ttrans u₂ u₄
Ttrans (u₁ ⊗ u₂) (u₃ ⊗ u₄) = Ttrans u₁ u₃ ⊗ Ttrans u₂ u₄
Ttrans (μ u₁) (μ u₂)       = μ (Ttrans u₁ u₂)
Ttrans (u₁ ⇒ u₂) (u₃ ⇒ u₄) = Ttrans u₁ u₃ ⇒ Ttrans u₂ u₄
Ttrans (ν u₁) (ν u₂)       = ν (Ttrans u₁ u₂)

≡→≅T : ∀ {Γ : Ctx} {t₁ t₂ : Type Γ} →
       t₁ ≡ t₂ → t₁ ≅T t₂
≡→≅T {Γ} {t₁} {.t₁} refl = Trefl

-- Note: makes the equality homogeneous in Γ
≅T-setoid : ∀ {Γ} → Setoid _ _
≅T-setoid {Γ} = record
  { Carrier = Type Γ
  ; _≈_ = _≅T_
  ; isEquivalence = record
    { refl = Trefl ; sym = Tsym ; trans = Ttrans }
  }

-- | Ground type
GType = Type []
unit′ : GType
unit′ = unit

-- | Variable renaming in types
rename : {Γ Δ : TyCtx} → (ρ : Γ ▹ Δ) → Type Γ → Type Δ
rename         ρ unit      = unit
rename         ρ (var x)   = var (ρ ∗ x)
rename         ρ (t₁ ⊕ t₂) = rename ρ t₁ ⊕ rename ρ t₂
rename {Γ} {Δ} ρ (μ t)     = μ (rename ρ' t)
  where
    ρ' : (∗ ∷ Γ) ▹ (∗ ∷ Δ)
    ρ' = ctx-id {[ ∗ ]} ⧻ ρ
rename         ρ (t₁ ⊗ t₂) = rename ρ t₁ ⊗ rename ρ t₂
rename         ρ (t₁ ⇒ t₂) = t₁ ⇒ rename ρ t₂
rename {Γ} {Δ} ρ (ν t)     = ν (rename ρ' t)
  where
    ρ' : (∗ ∷ Γ) ▹ (∗ ∷ Δ)
    ρ' = ctx-id {[ ∗ ]} ⧻ ρ

-------------------------
---- Generating structure on contexts (derived from renaming)

weaken : {Γ : TyCtx} (Δ : TyCtx) → Type Γ -> Type (Δ ∐ Γ)
weaken {Γ} Δ = rename {Γ} {Δ ∐ Γ} (i₂ {Δ} {Γ})

exchange : (Γ Δ : TyCtx) → Type (Γ ∐ Δ) -> Type (Δ ∐ Γ)
exchange Γ Δ = rename [ i₂ {Δ} {Γ} , i₁ {Δ} {Γ} ]

contract : {Γ : TyCtx} → Type (Γ ∐ Γ) -> Type Γ
contract = rename [ ctx-id , ctx-id ]

-- weaken-id-empty-ctx : (Δ : TyCtx) (t : GType) → weaken {[]} Δ t ≡ t
-- weaken-id-empty-ctx = ?

Subst : TyCtx → TyCtx → Set
Subst Γ Δ = TyVar Γ → Type Δ

id-subst : ∀{Γ : TyCtx} → Subst Γ Γ
id-subst x = var x

update : ∀{Γ Δ : TyCtx} → Subst Γ Δ → Type Δ → (Subst (∗ ∷ Γ) Δ)
update σ a zero        = a
update σ _ (succ′ _ x) = σ x

single-subst : ∀{Γ : TyCtx} → Type Γ → (Subst (∗ ∷ Γ) Γ)
single-subst a zero        = a
single-subst _ (succ′ _ x) = var x

lift : ∀{Γ Δ} → Subst Γ Δ → Subst (∗ ∷ Γ) (∗ ∷ Δ)
lift σ = update (weaken [ ∗ ] ∘ σ) (var zero)

-- | Simultaneous substitution
subst : {Γ Δ : TyCtx} → (σ : Subst Γ Δ) → Type Γ → Type Δ
subst         σ unit      = unit
subst         σ (var x)   = σ x
subst         σ (t₁ ⊕ t₂) = subst σ t₁ ⊕ subst σ t₂
subst {Γ} {Δ} σ (μ t)     = μ (subst (lift σ) t)
subst         σ (t₁ ⊗ t₂) = subst σ t₁ ⊗ subst σ t₂
subst         σ (t₁ ⇒ t₂) = t₁ ⇒ subst σ t₂
subst {Γ} {Δ} σ (ν t)     = ν (subst (lift σ) t)

subst₀ : {Γ : TyCtx} → Type Γ → Type (∗ ∷ Γ) → Type Γ
subst₀ {Γ} a = subst (update id-subst a)

rename′ : {Γ Δ : TyCtx} → (ρ : Γ ▹ Δ) → Type Γ → Type Δ
rename′ ρ = subst (var ∘ (ρ ∗))

-- | Unfold lfp
unfold-μ : (Type [ ∗ ]) → GType
unfold-μ a = subst₀ (μ a) a

-- | Unfold gfp
unfold-ν : (Type [ ∗ ]) → GType
unfold-ν a = subst₀ (ν a) a


--------------------------------------------------
---- Examples

Nat : Type []
Nat = μ (unit ⊕ x)
  where x = var zero

Str-Fun : {Γ : TyCtx} → Type Γ → Type (∗ ∷ Γ)
Str-Fun a = (weaken [ ∗ ] a ⊗ x)
  where x = var zero

Str : {Γ : TyCtx} → Type Γ → Type Γ
Str a = ν (Str-Fun a)

lemma : ∀ {Γ : Ctx} {a b : Type Γ} {σ : Subst Γ Γ} →
        subst (update σ b) (weaken [ ∗ ] a) ≅T subst σ a
lemma {a = unit}    = unit
lemma {a = var x}   = Trefl
lemma {a = a₁ ⊕ a₂} = lemma {a = a₁} ⊕ lemma {a = a₂}
lemma {a = μ a}     = μ {!!}
lemma {a = a₁ ⊗ a₂} = lemma {a = a₁} ⊗ lemma {a = a₂}
lemma {a = a₁ ⇒ a₂} = Trefl ⇒ lemma {a = a₂}
lemma {a = ν a}     = ν {!!}

lift-id-is-id-ext : ∀ {Γ : Ctx} (x : TyVar (∗ ∷ Γ)) →
                    (lift (id-subst {Γ})) x ≡ id-subst x
lift-id-is-id-ext zero        = refl
lift-id-is-id-ext (succ′ ∗ x) = refl

lift-id-is-id : ∀ {Γ : Ctx} → lift (id-subst {Γ}) ≡ id-subst
lift-id-is-id = η-≡ lift-id-is-id-ext

id-subst-id : ∀ {Γ : Ctx} {a : Type Γ} →
              subst id-subst a ≅T a
id-subst-id {a = unit}   = unit
id-subst-id {a = var x}  = var Vrefl
id-subst-id {a = a ⊕ a₁} = id-subst-id ⊕ id-subst-id
id-subst-id {a = μ a}    =
  μ (Ttrans (≡→≅T (cong (λ u → subst u a) lift-id-is-id)) id-subst-id)
id-subst-id {a = a ⊗ a₁} = id-subst-id ⊗ id-subst-id
id-subst-id {a = a ⇒ a₁} = Trefl ⇒ id-subst-id
id-subst-id {a = ν a}    =
  ν (Ttrans (≡→≅T (cong (λ u → subst u a) lift-id-is-id)) id-subst-id)


lemma₂ : ∀ {Γ : Ctx} {a b : Type Γ} →
        subst (update id-subst b) (weaken [ ∗ ] a) ≅T a
lemma₂ {Γ} {a} {b} = Ttrans (lemma {Γ} {a} {b} {σ = id-subst}) id-subst-id

unfold-str : ∀{a : Type []} → (unfold-ν (Str-Fun a)) ≅T (a ⊗ Str a)
unfold-str {a} = lemma₂ ⊗ Trefl

LFair : {Γ : TyCtx} → Type Γ → Type Γ → Type Γ
LFair a b = ν (μ ((w a ⊗ x) ⊕ (w b ⊗ y)))
  where
    x = var zero
    y = var (succ zero)
    Δ = ∗ ∷ [ ∗ ]
    w = weaken Δ
