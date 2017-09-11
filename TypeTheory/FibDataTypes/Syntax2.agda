module Syntax2 where

import Level
open import Data.Empty
open import Data.Unit as Unit renaming (tt to ∗)
open import Data.Nat
open import Data.List as List renaming ([] to Ø) hiding ([_])
open import NonEmptyList as NList
open import Data.Vec as Vec hiding ([_]; _++_)
open import Data.Product as Prod
open import Categories.Category using (Category)
open import Function

open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import Relation.Binary using (module IsEquivalence; Setoid; module Setoid)
open ≡-Reasoning

open import Common.Context as Context

Univ = ⊤

length' : {A : Set} → List A → ℕ
length' Ø = 0
length' (x ∷ xs) = suc (length' xs)

data FP : Set where
  μ : FP
  ν : FP

RawCtx : Set
RawCtx = Ctx ⊤

RawVar : RawCtx → Set
RawVar Γ = Var Γ ∗

TyCtx : Set
TyCtx = Ctx RawCtx

TyVar : TyCtx → RawCtx → Set
TyVar = Var

CtxMor : (TyCtx → RawCtx → RawCtx → Set) → RawCtx → RawCtx → Set
CtxMor R Γ₁ Γ₂ = Vec (R Ø Γ₁ Ø) (length' Γ₂)

FpData : (TyCtx → RawCtx → RawCtx → Set) → TyCtx → RawCtx → Set
FpData R Θ Γ = NList (Σ RawCtx (λ Γ' → CtxMor R Γ' Γ × R (Γ ∷ Θ) Γ' Ø))

FpMapData : (TyCtx → RawCtx → RawCtx → Set) → Set
FpMapData R = NList (Σ RawCtx λ Γ' → R Ø (∗ ∷ Γ') Ø)

-- | Types and objects with their corresponding (untyped) type, object
-- variable contexts and parameter contexts.
data Raw : TyCtx → RawCtx → RawCtx → Set where
  ----- Common constructors
  instRaw : {Θ : TyCtx} {Γ₁ Γ₂ : RawCtx} →
            Raw Θ Γ₁ (∗ ∷ Γ₂) → Raw Ø Γ₁ Ø → Raw Θ Γ₁ Γ₂

  ----- Object constructors
  unitRaw : (Γ : RawCtx) → Raw Ø Γ Ø
  objVarRaw : (Γ : RawCtx) → RawVar Γ → Raw Ø Γ Ø
  dialgRaw : {Γ Γ' : RawCtx} (Δ : RawCtx) →
             CtxMor Raw Γ' Γ → Raw (Γ ∷ Ø) Γ' Ø → FP → Raw Ø Δ (∗ ∷ Γ')
  mappingRaw : (Γ Δ : RawCtx) →
               FpMapData Raw → FP → Raw Ø Δ Γ

  ----- Type constructors
  ⊤-Raw : (Θ : TyCtx) (Γ : RawCtx) → Raw Θ Γ Ø
  tyVarRaw : {Θ : TyCtx} (Γ₁ : RawCtx) {Γ₂ : RawCtx} → TyVar Θ Γ₂ → Raw Θ Γ₁ Γ₂
  paramAbstrRaw : {Θ : TyCtx} {Γ₂ : RawCtx} (Γ₁ : RawCtx) →
                  Raw Θ (∗ ∷ Γ₁) Γ₂ → Raw Θ Γ₁ (Γ₂ ++ ∗ ∷ Ø)
  -- | Constructor for fixed points. The first component is intended to be
  -- the context morphism, the second is the type.
  fpRaw : {Θ : TyCtx} {Γ₂ : RawCtx} (Γ₁ : RawCtx) →
          FP → FpData Raw Θ Γ₂ → Raw Θ Γ₁ Γ₂


weaken : {Θ : TyCtx} {Γ₁ Γ₂ : RawCtx} → Raw Θ Γ₁ Γ₂ → Raw Θ (∗ ∷ Γ₁) Γ₂
weaken (instRaw t s)        = instRaw (weaken t) (weaken s)
weaken (unitRaw Γ)          = unitRaw (∗ ∷ Γ)
weaken (objVarRaw Γ x)      = objVarRaw (∗ ∷ Γ) (succ ∗ x)
weaken (dialgRaw Δ f t ρ)   = dialgRaw (∗ ∷ Δ) f t ρ
weaken (mappingRaw Γ Δ gs ρ)  = mappingRaw Γ (∗ ∷ Δ) gs ρ
weaken (⊤-Raw Θ Γ)          = ⊤-Raw Θ (∗ ∷ Γ)
weaken (tyVarRaw Γ₁ X)      = tyVarRaw (∗ ∷ Γ₁) X
weaken (paramAbstrRaw Γ₁ A) = paramAbstrRaw (∗ ∷ Γ₁) (weaken A)
weaken (fpRaw Γ₁ ρ D)       = fpRaw (∗ ∷ Γ₁) ρ D

ctxid : (Γ : RawCtx) → CtxMor Raw Γ Γ
ctxid Ø = []
ctxid (x ∷ Γ) = (objVarRaw (∗ ∷ Γ) zero) ∷ (Vec.map weaken (ctxid Γ))

-- | Build the instantiation "t f" of a raw term t by a context morphism f
instWCtxMor : {Θ : TyCtx} {Γ₁ Γ₂ : RawCtx} →
              Raw Θ Γ₁ Γ₂ → CtxMor Raw Γ₁ Γ₂ → Raw Θ Γ₁ Ø
instWCtxMor {Γ₂ = Ø}      t []      = t
instWCtxMor {Γ₂ = x ∷ Γ₂} t (s ∷ f) = instWCtxMor (instRaw t s) f

-- | Retrieve the term to be substituted for a variable from a context morphism
get : {R : TyCtx → RawCtx → RawCtx → Set} {Γ₁ Γ₂ : RawCtx} →
      CtxMor R Γ₂ Γ₁ → RawVar Γ₁ → R Ø Γ₂ Ø
get {R} {Ø}       []     ()
get {R} {_ ∷ Γ₁} (M ∷ f) zero        = M
get {R} {_ ∷ Γ₁} (M ∷ f) (succ .∗ x) = get {R} f x

-- | Extends a context morphism to be the identity on a new variable
extend : {Γ₁ Γ₂ : RawCtx} → CtxMor Raw Γ₂ Γ₁ → CtxMor Raw (∗ ∷ Γ₂) (∗ ∷ Γ₁)
extend f = (objVarRaw _ zero) ∷ (Vec.map weaken f)

-- | Substitution on raw terms
substRaw : ∀ {Θ Γ₁ Γ Γ₂} → Raw Θ Γ₁ Γ → CtxMor Raw Γ₂ Γ₁ → Raw Θ Γ₂ Γ
substRaw (instRaw M N)        f = instRaw (substRaw M f) (substRaw N f)
substRaw (unitRaw Γ)          f = unitRaw _
substRaw (objVarRaw Γ₁ x)     f = get {Raw} f x
substRaw (dialgRaw Δ g A ρ)   f = dialgRaw _ g A ρ
substRaw (mappingRaw Γ Δ gs ρ)  f = mappingRaw _ _ gs ρ
substRaw (⊤-Raw Θ Γ)          f = ⊤-Raw Θ _
substRaw (tyVarRaw Γ₁ X)      f = tyVarRaw _ X
substRaw (paramAbstrRaw Γ₁ A) f = paramAbstrRaw _ (substRaw A (extend f))
substRaw (fpRaw Γ₁ ρ D)       f = fpRaw _ ρ D

substTyRaw₀ : ∀ {Θ Γ₁ Γ Γ₂} →
              Raw (Γ ∷ Θ) Γ₁ Γ₂ → Raw Ø Ø Γ → Raw Θ Γ₁ Γ₂
substTyRaw₀ (instRaw A t) B = instRaw (substTyRaw₀ A B) t
substTyRaw₀ (⊤-Raw ._ Γ₁) B = ⊤-Raw _ _
substTyRaw₀ (tyVarRaw Γ₁ zero) B = {!!}
substTyRaw₀ (tyVarRaw Γ₁ (succ Γ₂ X)) B = {!!}
substTyRaw₀ (paramAbstrRaw Γ₁ A) B = {!!}
substTyRaw₀ (fpRaw Γ₁ x x₁) B = {!!}

-- | Substitute into for type variables
substTyRaw : ∀ {Θ₁ Θ₂ Γ₁ Γ Γ₂} →
             Raw (Θ₁ ++ (Γ ∷ Θ₂)) Γ₁ Γ₂ → Raw Ø Ø Γ → Raw (Θ₁ ++ Θ₂) Γ₁ Γ₂
substTyRaw {Ø} A B = {!!}
substTyRaw {x ∷ Θ₁} A B = {!!}

-- | Context morphism that projects on arbitrary prefix of a context
ctxProjRaw : (Γ₁ Γ₂ : RawCtx) → CtxMor Raw (Γ₂ ++ Γ₁) Γ₁
ctxProjRaw Γ₁ Ø = ctxid Γ₁
ctxProjRaw Γ₁ (x ∷ Γ₂) = Vec.map weaken (ctxProjRaw Γ₁ Γ₂)

-- | Extend one step weakening to weakening by arbitrary contexts
weaken' : ∀ {Θ Γ₁ Γ₃} →
          (Γ₂ : RawCtx) → Raw Θ Γ₁ Γ₃ → Raw Θ (Γ₂ ++ Γ₁) Γ₃
weaken' {Γ₁ = Γ₁} Γ₂ t = substRaw t (ctxProjRaw Γ₁ Γ₂)

-----------------------------------------
--- Examples
-----------------------------------------

_︵_ : {A : Set} → A → A → List A
a ︵ b = a ∷ b ∷ Ø

-- | Binary product type
Prod : (Γ : RawCtx) → Raw (Γ ︵ Γ) Ø Γ
Prod Γ = fpRaw {Δ} {Γ} Ø ν D
  where
    Δ = Γ ︵ Γ

    A : TyVar (Γ ∷ Δ) Γ
    A = succ Γ zero

    B : TyVar (Γ ∷ Δ) Γ
    B = succ Γ (succ Γ zero)

    D₁ = (Γ , ctxid Γ , instWCtxMor (tyVarRaw Γ A) (ctxid Γ))

    D₂ = (Γ , ctxid Γ , instWCtxMor (tyVarRaw Γ B) (ctxid Γ))

    D : FpData Raw Δ Γ
    D = D₁ ∷ [ D₂ ]


-----------------------------------------
--- Separate types and terms
-----------------------------------------

mutual
  data DecentType : {Θ : TyCtx} {Γ₁ Γ₂ : RawCtx} → Raw Θ Γ₁ Γ₂ → Set where
    DT-⊤ : (Θ : TyCtx) (Γ : RawCtx) → DecentType (⊤-Raw Θ Γ)
    DT-tyVar : {Θ : TyCtx} (Γ₁ : RawCtx) {Γ₂ : RawCtx} →
               (X : TyVar Θ Γ₂) → DecentType (tyVarRaw Γ₁ X)
    DT-inst : ∀{Θ Γ₁ Γ₂} →
              (A : Raw Θ Γ₁ (∗ ∷ Γ₂)) → (t : Raw Ø Γ₁ Ø) →
              DecentType A → DecentTerm t →
              DecentType (instRaw A t)
    DT-paramAbstr : ∀{Θ Γ₂} (Γ₁ : RawCtx) →
                    (A : Raw Θ (∗ ∷ Γ₁) Γ₂) →
                    DecentType A →
                    DecentType (paramAbstrRaw Γ₁ A)
    DT-fp : ∀{Θ Γ₂} (Γ₁ : RawCtx) →
            (ρ : FP) → (D : FpData Raw Θ Γ₂) →
            DecentFpData D →
            DecentType (fpRaw Γ₁ ρ D)

  data DecentTerm : {Γ₁ Γ₂ : RawCtx} → Raw Ø Γ₁ Γ₂ → Set where
    DO-unit : (Γ : RawCtx) → DecentTerm (unitRaw Γ)
    DO-objVar : (Γ : RawCtx) → (x : RawVar Γ) → DecentTerm (objVarRaw Γ x)
    DO-inst : {Γ₁ Γ₂ : RawCtx} →
              (t : Raw Ø Γ₁ (∗ ∷ Γ₂)) → (s : Raw Ø Γ₁ Ø) →
              DecentTerm t → DecentTerm s →
              DecentTerm (instRaw t s)
    DO-dialg : {Γ Γ' : RawCtx} (Δ : RawCtx) →
               (f : CtxMor Raw Γ' Γ) → (A : Raw (Γ ∷ Ø) Γ' Ø) → (ρ : FP) →
               DecentCtxMor f → DecentType A →
               DecentTerm (dialgRaw Δ f A ρ)
    DO-mapping : {Γ : RawCtx} (Δ : RawCtx) →
                 (gs : FpMapData Raw) → (ρ : FP) →
                 DecentTermList gs →
                 DecentTerm (mappingRaw Γ Δ gs ρ)

  DecentTermList : FpMapData Raw → Set
  DecentTermList [ (Γ' , t) ] = DecentTerm t
  DecentTermList ((Γ' , t) ∷ ts) = DecentTerm t × DecentTermList ts

  DecentCtxMor : {Γ₁ Γ₂ : RawCtx} → CtxMor Raw Γ₁ Γ₂ → Set
  DecentCtxMor {Γ₂ = Ø}      []      = ⊤
  DecentCtxMor {Γ₂ = x ∷ Γ₂} (t ∷ f) = DecentTerm t × DecentCtxMor f

  DecentFpData : ∀{Θ Γ₂} → FpData Raw Θ Γ₂ → Set
  DecentFpData [ Γ , f , A ] = DecentCtxMor f × DecentType A
  DecentFpData ((Γ , f , A) ∷ D)
    = (DecentCtxMor f × DecentType A) × DecentFpData D

weakenDO : {Γ₁ Γ₂ : RawCtx} {t : Raw Ø Γ₁ Γ₂} →
           DecentTerm t → DecentTerm (weaken t)

weakenDT : ∀ {Θ Γ₁ Γ₂} {A : Raw Θ Γ₁ Γ₂} →
           DecentType A → DecentType (weaken A)
weakenDT (DT-⊤ Θ Γ)             = DT-⊤ Θ _
weakenDT (DT-tyVar Γ₁ X)        = DT-tyVar _ X
weakenDT (DT-inst A t p q)      = DT-inst _ _ (weakenDT p) (weakenDO q)
weakenDT (DT-paramAbstr Γ₁ A p) = DT-paramAbstr _ _ (weakenDT p)
weakenDT (DT-fp Γ₁ ρ D p)       = DT-fp _ ρ D p

weakenDO (DO-unit Γ)            = DO-unit _
weakenDO (DO-objVar Γ x)        = DO-objVar _ (succ ∗ x)
weakenDO (DO-inst t s p q)      = DO-inst _ _ (weakenDO p) (weakenDO q)
weakenDO (DO-dialg Δ f A ρ p q) = DO-dialg _ f _ ρ p q
weakenDO (DO-mapping Δ gs ρ p)  = DO-mapping _ gs ρ p

weakenDecentCtxMor : {Γ₁ Γ₂ : RawCtx} {f : CtxMor Raw Γ₁ Γ₂} →
                     DecentCtxMor f → DecentCtxMor (Vec.map weaken f)
weakenDecentCtxMor {Γ₂ = Ø}      {f}     p        = ∗
weakenDecentCtxMor {Γ₂ = x ∷ Γ₂} {t ∷ f} (p , ps) =
  (weakenDO p , weakenDecentCtxMor ps)

-------------------------------------
------- Pre-types and terms
-------------------------------------

PreType : (Θ : TyCtx) (Γ₁ Γ₂ : RawCtx) → Set
PreType Θ Γ₁ Γ₂ = Σ (Raw Θ Γ₁ Γ₂) λ A → DecentType A

mkPreType : ∀ {Θ Γ₁ Γ₂} {A : Raw Θ Γ₁ Γ₂} → DecentType A → PreType Θ Γ₁ Γ₂
mkPreType {A = A} p = (A , p)

PreTerm : (Γ₁ Γ₂ : RawCtx) → Set
PreTerm Γ₁ Γ₂ = Σ (Raw Ø Γ₁ Γ₂) λ t → DecentTerm t

mkPreTerm : ∀ {Γ₁ Γ₂} {t : Raw Ø Γ₁ Γ₂} → DecentTerm t → PreTerm Γ₁ Γ₂
mkPreTerm {t = t} p = (t , p)

CtxMorP = CtxMor (λ _ → PreTerm)
FpMapDataP = FpMapData (λ _ → PreTerm)

mkCtxMorP : {Γ₁ Γ₂ : RawCtx} {f : CtxMor Raw Γ₁ Γ₂} →
             DecentCtxMor f → CtxMorP Γ₁ Γ₂
mkCtxMorP {Γ₂ = Ø}              p        = []
mkCtxMorP {Γ₂ = x ∷ Γ₂} {t ∷ f} (p , ps) = (t , p) ∷ (mkCtxMorP ps)

projCtxMor₁ : {Γ₁ Γ₂ : RawCtx} → CtxMorP Γ₂ Γ₁ → CtxMor Raw Γ₂ Γ₁
projCtxMor₁ = Vec.map proj₁

projCtxMor₂ : {Γ₁ Γ₂ : RawCtx} →
              (f : CtxMorP Γ₂ Γ₁) →  DecentCtxMor (projCtxMor₁ f)
projCtxMor₂ {Ø} [] = ∗
projCtxMor₂ {x ∷ Γ₁} ((t , p) ∷ f) = (p , projCtxMor₂ f)

projPTList₁ : FpMapDataP → FpMapData Raw
projPTList₁ = NList.map (Prod.map id proj₁)

projPTList₂ : (gs : FpMapDataP) → DecentTermList (projPTList₁ gs)
projPTList₂ [ (Γ' , t , p) ] = p
projPTList₂ ((Γ' , t , p) ∷ gs) = (p , projPTList₂ gs)

-----------------------------------------
----- Constructors for pre terms
-----------------------------------------

unitPT : (Γ : RawCtx) → PreTerm Γ Ø
unitPT Γ = mkPreTerm (DO-unit _)

varPT : (Γ : RawCtx) → RawVar Γ → PreTerm Γ Ø
varPT Γ x = mkPreTerm (DO-objVar _ x)

instPT : {Γ₁ : RawCtx} {Γ₂ : RawCtx} →
         PreTerm Γ₁ (∗ ∷ Γ₂) → PreTerm Γ₁ Ø → PreTerm Γ₁ Γ₂
instPT (t , p) (s , q) = mkPreTerm (DO-inst _ _ p q)

dialgPT : {Γ Γ' : RawCtx} (Δ : RawCtx) →
          CtxMorP Γ' Γ → PreType (Γ ∷ Ø) Γ' Ø → FP → PreTerm Δ (∗ ∷ Γ')
dialgPT Δ f (A , p) ρ = mkPreTerm (DO-dialg _ _ _ ρ (projCtxMor₂ f) p)

mappingPT : {Γ : RawCtx} (Δ : RawCtx) →
            FpMapDataP → FP → PreTerm Δ Γ
mappingPT Δ gs ρ = mkPreTerm (DO-mapping _ _ ρ (projPTList₂ gs))

instWCtxMorP : {Γ₁ Γ₂ : RawCtx} →
               PreTerm Γ₁ Γ₂ → CtxMorP Γ₁ Γ₂ → PreTerm Γ₁ Ø
instWCtxMorP {Γ₂ = Ø}      M []      = M
instWCtxMorP {Γ₂ = x ∷ Γ₂} M (N ∷ f) = instWCtxMorP (instPT M N) f


-----------------------------------------------------
------ Meta operations on pre-terms and pre-types
-----------------------------------------------------

weakenPT : ∀ {Θ Γ₁ Γ₂} → PreType Θ Γ₁ Γ₂ → PreType Θ (∗ ∷ Γ₁) Γ₂
weakenPT (A , p) = (weaken A , weakenDT p)

weakenPO : {Γ₁ Γ₂ : RawCtx} → PreTerm Γ₁ Γ₂ → PreTerm (∗ ∷ Γ₁) Γ₂
weakenPO (t , p) = (weaken t , weakenDO p)

get' : {Γ₁ Γ₂ : RawCtx} →
       (f : CtxMor (λ _ → PreTerm) Γ₂ Γ₁) →
       (x : RawVar Γ₁) →
       DecentTerm (get {Raw} (projCtxMor₁ f) x)
get' (t ∷ f) zero                = proj₂ t
get' (t ∷ f) (succ {b = ∗} .∗ x) = get' f x

-- | Lift substitutions to DecentTerm predicate
substDO : {Γ₁ Γ Γ₂ : RawCtx} {t : Raw Ø Γ₁ Γ} →
          (f : CtxMorP Γ₂ Γ₁) →
          DecentTerm t → DecentTerm (substRaw t (projCtxMor₁ f))
substDO f (DO-unit Γ₁)              = DO-unit _
substDO f (DO-objVar Γ₁ x)          = get' f x
substDO f (DO-inst t s p q)         = DO-inst _ _ (substDO f p) (substDO f q)
substDO f (DO-dialg Γ₁ g A ρ p q)   = DO-dialg _ _ _ _ p q
substDO f (DO-mapping Γ₁ gs ρ p)    = DO-mapping _ _ _ p

-- | Lift substRaw to pre terms
substP : {Γ₁ Γ Γ₂ : RawCtx} →
         PreTerm Γ₁ Γ → CtxMorP Γ₂ Γ₁ → PreTerm Γ₂ Γ
substP (t , p) f = (substRaw t (projCtxMor₁ f) , substDO f p)

-- | Context identity is a decent context morphism
ctxidDO : (Γ : RawCtx) → DecentCtxMor (ctxid Γ)
ctxidDO Ø       = ∗
ctxidDO (x ∷ Γ) = (DO-objVar _ zero , weakenDecentCtxMor (ctxidDO Γ))

mkCtxMorP₁ : {Γ₁ Γ₂ : RawCtx} {f : CtxMor Raw Γ₁ Γ₂} →
             (p : DecentCtxMor f) → projCtxMor₁ (mkCtxMorP p) ≡ f
mkCtxMorP₁ {Γ₂ = Ø}      {[]} p = refl
mkCtxMorP₁ {Γ₂ = x ∷ Γ₂} {t ∷ f} (p , ps) =
  begin
    projCtxMor₁ ((t , p) ∷ mkCtxMorP ps)
  ≡⟨ refl ⟩
    t ∷ projCtxMor₁ (mkCtxMorP ps)
  ≡⟨ cong (λ u → t ∷ u) (mkCtxMorP₁ ps) ⟩
    t ∷ f
  ∎

ctxidP : (Γ : RawCtx) → CtxMorP Γ Γ
ctxidP Γ = mkCtxMorP (ctxidDO Γ)

-- | Context projection is a decent context morphism
ctxProjDO : (Γ₁ Γ₂ : RawCtx) → DecentCtxMor (ctxProjRaw Γ₁ Γ₂)
ctxProjDO Γ₁ Ø        = ctxidDO Γ₁
ctxProjDO Γ₁ (x ∷ Γ₂) = weakenDecentCtxMor (ctxProjDO Γ₁ Γ₂)

ctxProjP : (Γ₁ Γ₂ : RawCtx) → CtxMorP (Γ₂ ++ Γ₁) Γ₁
ctxProjP Γ₁ Γ₂ = mkCtxMorP (ctxProjDO Γ₁ Γ₂)

weakenDO' : {Γ₁ Γ₃ : RawCtx} {t : Raw Ø Γ₁ Γ₃} →
            (Γ₂ : RawCtx) → DecentTerm t → DecentTerm (weaken' Γ₂ t)
weakenDO' {Γ₁} {t = t} Γ₂ p =
  subst DecentTerm
        (cong (substRaw t) (mkCtxMorP₁ (ctxProjDO Γ₁ Γ₂)))
        (substDO (ctxProjP Γ₁ Γ₂) p)

weakenPO' : {Γ₁ Γ₃ : RawCtx} →
            (Γ₂ : RawCtx) → PreTerm Γ₁ Γ₃ → PreTerm (Γ₂ ++ Γ₁) Γ₃
weakenPO' Γ₂ (t , p) = (weaken' Γ₂ t , weakenDO' Γ₂ p)

weakenPO'' : {Γ₁ Γ₃ : RawCtx} →
            (Γ₂ Γ₂' : RawCtx) → PreTerm Γ₁ Γ₃ → PreTerm (Γ₂' ++ Γ₁ ++ Γ₂) Γ₃
weakenPO'' = {!!}

-- | Project a specific variable out
projVar : (Γ₁ Γ₂ : RawCtx) → PreTerm (Γ₂ ++ ∗ ∷ Γ₁) Ø
projVar Γ₁ Ø        = varPT _ zero
projVar Γ₁ (∗ ∷ Γ₂) = weakenPO (projVar Γ₁ Γ₂)

-----------------------------------------------------
---- Action of types on terms
-----------------------------------------------------

shift-lemma : {A : Set} → (x y : List A) → (a : A) →
              x ++ (a ∷ y) ≡ (x ++ a ∷ Ø) ++ y
shift-lemma Ø       y a = refl
shift-lemma (b ∷ x) y a = cong (_∷_ b) (shift-lemma x y a)

Args : TyCtx → Set
Args Ø = ⊥
Args (Γ ∷ Θ) = (PreTerm (∗ ∷ Γ) Ø) × (Args Θ)

getArg : ∀ {Θ Γ₁} → TyVar Θ Γ₁ → Args Θ → PreTerm (∗ ∷ Γ₁) Ø
getArg zero        (t , ts) = t
getArg (succ Γ₁ X) (t , ts) = getArg X ts

substArgCodomTypes : ∀ {Θ Γ Γ₁} →
                Args Θ → PreType (Γ ∷ Θ) Γ₁ Ø → PreType (Γ ∷ Ø) Γ₁ Ø
substArgCodomTypes {Ø} () A
substArgCodomTypes {Γ ∷ Θ} (M , a) A = {!!}

{-# NON_TERMINATING #-}
⟪_⟫ : ∀ {Θ Γ₁ Γ₂} → PreType Θ Γ₁ Γ₂ → Args Θ → PreTerm (∗ ∷ Γ₂ ++ Γ₁) Ø
⟪_⟫ {Θ} {Γ₁} (instRaw {Γ₂ = Γ₂} A t , DT-inst .A .t dt-A do-t) ts =
  substP (⟪ A , dt-A ⟫ ts) f
  where
    -- | Substitute t for the second variable, i.e., f = (id, t, x).
    f : CtxMorP (∗ ∷ Γ₂ ++ Γ₁) (∗ ∷ ∗ ∷ Γ₂ ++ Γ₁)
    f = (varPT (∗ ∷ Γ₂ ++ Γ₁) zero)
        ∷ weakenPO' (∗ ∷ Γ₂) (t , do-t)
        ∷ ctxProjP (Γ₂ ++ Γ₁) (∗ ∷ Ø)
⟪ unitRaw Γ         , () ⟫ ts
⟪ objVarRaw Γ x     , () ⟫ ts
⟪ dialgRaw Δ x A x₁ , () ⟫ ts
⟪ mappingRaw Γ Δ x x₁ , () ⟫ ts
⟪ ⊤-Raw Θ Γ , DT-⊤ .Θ .Γ ⟫ ts = ((objVarRaw (∗ ∷ Γ) zero) , (DO-objVar _ _))
⟪ tyVarRaw Γ₁ X , DT-tyVar .Γ₁ .X ⟫ ts = weakenPO'' Γ₁ Ø (getArg X ts)
⟪ paramAbstrRaw {Γ₂ = Γ₂} Γ₁ A , DT-paramAbstr .Γ₁ .A p ⟫ ts =
  subst (λ u → PreTerm u Ø)
        (cong (_∷_ ∗) (shift-lemma Γ₂ Γ₁ ∗))
        (⟪ A , p ⟫ ts)
⟪ fpRaw {Θ} {Γ₂} Γ₁ μ D , DT-fp .Γ₁ .μ .D p ⟫ ts =
  instWCtxMorP (mappingPT _ (gs D p) μ) (ctxidP _)
  where
    -- Construction of gₖ = αₖ id (⟪ Bₖ ⟫ (ts, id))
    mkBase : ∀{Γ'} (x : CtxMor Raw Γ' Γ₂ × Raw (Γ₂ ∷ Θ) Γ' Ø) →
             (f : DecentCtxMor (proj₁ x)) →
             (A : DecentType (proj₂ x)) →
             Σ RawCtx (λ Γ' → PreTerm (∗ ∷ Γ') Ø)
    mkBase {Γ'} x f A = (Γ' , instWCtxMorP α r)
      where
        B : PreType (Γ₂ ∷ Θ) Γ' Ø
        B = mkPreType A

        A₂ : PreType (Γ₂ ∷ Ø) Γ' Ø
        A₂ = substArgCodomTypes ts B

        α : PreTerm (∗ ∷ Γ') (∗ ∷ Γ')
        α = dialgPT _ (mkCtxMorP f) A₂ μ

        r : CtxMorP (∗ ∷ Γ') (∗ ∷ Γ')
        r = (⟪ B ⟫ ((varPT _ zero) , ts)) ∷ ctxProjP Γ' (∗ ∷ Ø)

    -- Construct the g₁, ..., gₙ used in the recursion
    gs : (D : FpData Raw Θ Γ₂) → DecentFpData D → FpMapDataP
    gs [ Γ' , x ] (f , A) = [ mkBase x f A ]
    gs ((Γ' , x) ∷ D₁) ((f , A) , p₁) = mkBase x f A ∷ gs D₁ p₁

⟪_⟫ (fpRaw Γ₁ ν x₁ , DT-fp .Γ₁ .ν .x₁ x) ts = {!!}

-----------------------------------------------------
---- Reduction relation on pre-types and pre-terms
-----------------------------------------------------

data _≻_  : {Γ₁ Γ₂ : RawCtx} → (t s : PreTerm Γ₁ Γ₂) → Set where
  contract-rec : {Γ : RawCtx} → (gs : NList (PreTerm (∗ ∷ Γ) Ø)) →
    instPT
      (mappingPT {!!} {!!} μ)
      (instPT (dialgPT {!!} {!!} {!!} μ) {!!})
    ≻ {!!}
