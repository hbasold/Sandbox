module Terms where

import Level
open import Data.Unit as Unit
open import Data.List as List
open import Data.Product as Product
open import Categories.Category using (Category)

open import Types

open import Context GType
  using (Ctx; Var; zero; ctx-cat; ctx-bin-coproducts)
  renaming (succ to succ′)
open Categories.Category.Category ctx-cat
  renaming ( _⇒_ to _▹_
           ; _≡_ to _≈_
           ; _∘_ to _●_
           ; id  to ctx-id
           )
open import Categories.Object.BinaryCoproducts ctx-cat
open BinaryCoproducts ctx-bin-coproducts

-- | Signatures over which we can define terms
Sig = Ctx

-- | Typed patterns
data Pat : (a : GType) → Set where
  〈〉′  : Pat unit
  var′ : ∀{a : GType}       (x : Var [ a ] a)                 → Pat a
  κ₁′  : ∀{a₁ a₂ : GType}   (p : Pat a₁)           → Pat (a₁ ⊕ a₂)
  κ₂′  : ∀{a₁ a₂ : GType}   (p : Pat a₂)           → Pat (a₁ ⊕ a₂)
  α′   : ∀{a : Type [ tt ]} (p : Pat (unfold-μ a)) → Pat (μ a)

-- | Context defined by a pattern (this is either empty or contains a single
--   variable).
pat-ctx : ∀ {a} → Pat a → Ctx
pat-ctx     〈〉′      = []
pat-ctx {a} (var′ x) = [ a ]
pat-ctx     (κ₁′ x)  = pat-ctx x
pat-ctx     (κ₂′ x)  = pat-ctx x
pat-ctx     (α′ x)   = pat-ctx x

-- | Typed copatterns
data Copat : (a b : GType) → Set where
  ·    : ∀{a}                                                   → Copat a a
  app′ : ∀{a b c : GType}               (q : Copat (b ⇒ c) a)
                                        (p : Pat c)             → Copat c a
  π₁′  : ∀{a₁ a₂ a : GType}             (q : Copat (a₁ ⊗ a₂) a) → Copat a₁ a
  π₂′  : ∀{a₁ a₂ a : GType}             (q : Copat (a₁ ⊗ a₂) a) → Copat a₂ a
  ξ′   : ∀{b : Type [ tt ]} {a : GType} (q : Copat (ν b) a)     → Copat (unfold-ν b) a

-- | Context defined by a copattern
copat-ctx : ∀ { a b} → Copat a b → Ctx
copat-ctx ·          = []
copat-ctx (app′ q p) = (copat-ctx q) ∐ (pat-ctx p)
copat-ctx (π₁′ q)    = copat-ctx q
copat-ctx (π₂′ q)    = copat-ctx q
copat-ctx (ξ′ q)     = copat-ctx q

mutual
  -- | A clause { q₁ ↦ t₁ ; ... ; qₙ ↦ tₙ } defines the body of a λ-abstraction
  --   of the definition of a symbol in a signature.
  record Clause {Δ : Sig} {Γ : Ctx} {a : GType} : Set where
    field
      body : List (
                  Σ GType (λ b →
                  Σ (Copat a b) (λ q →
                    (Term {Δ} ((copat-ctx q) ∐ Γ) b)))
             )

  -- | Terms typed in a context
  data Term {Δ : Sig} (Γ : Ctx) : (a : GType) → Set where
    〈〉    :                                                   Term Γ unit′
    var  : ∀{a : GType}       (x : Var Γ a)                 → Term Γ a
    κ₁   : ∀{a₁ a₂ : GType}   (t : Term {Δ} Γ a₁)           → Term Γ (a₁ ⊕ a₂)
    κ₂   : ∀{a₁ a₂ : GType}   (t : Term {Δ} Γ a₂)           → Term Γ (a₁ ⊕ a₂)
    α    : ∀{a : Type [ tt ]} (t : Term {Δ} Γ (unfold-μ a)) → Term Γ (μ a)
    app  : ∀{a b : GType}     (t : Term {Δ} Γ (a ⇒ b))
                              (s : Term {Δ} Γ a)            → Term Γ b
    π₁   : ∀{a₁ a₂ : GType}   (t : Term {Δ} Γ (a₁ ⊗ a₂))    → Term Γ a₁
    π₂   : ∀{a₁ a₂ : GType}   (t : Term {Δ} Γ (a₁ ⊗ a₂))    → Term Γ a₂
    ξ    : ∀{a : Type [ tt ]} (t : Term {Δ} Γ (ν a))        → Term Γ (unfold-ν a)
    svar : ∀{a : GType}       (f : Var Δ a)                 → Term Γ a
    abs  : ∀{a : GType}       (D : Clause {Δ} {Γ} {a})      → Term Γ a

-- | A definition consists of a signature and its definition
record Definition (Δ : Sig) : Set where
  field
    defs : List (Σ GType (λ a → (Var Δ a) × Clause {Δ} {[]} {a}))
open Definition

TermWDef : GType → Set
TermWDef a = Σ Sig (λ Δ → (Definition Δ) × (Term {Δ} [] a))

---------- Convenience
_↦_ : ∀{Δ : Sig} {Γ : Ctx} {a b : GType}
          (q : Copat a b) (t : Term {Δ} ((copat-ctx q) ∐ Γ) b) →
            (Σ GType (λ b →
              Σ (Copat a b) (λ q →
              (Term {Δ} ((copat-ctx q) ∐ Γ) b))))
_↦_ {b = b} q t = b , q , t

_≝_ : ∀{Δ : Sig} {a : GType}
      (f : Var Δ a) (c : Clause {Δ} {[]} {a}) →
        Σ GType (λ a → (Var Δ a) × Clause {Δ} {[]} {a})
_≝_ {a = a} f c = a , (f , c)

--------------------------------
------ Examples

hd : ∀ {a : GType} → Term (Str a) → Term a
hd t = π₁ (ξ q)


hd′ : ∀ {a b : GType} → Copat (Str a) b → Copat a b
hd′ q = π₁′ (ξ′ q)

ones : TermWDef (Str Nat)
ones = Δ , def , (svar o)
  where
    Δ : Sig
    Δ = [ Str Nat ]
    o : Var [ Str Nat ] (Str Nat)
    o = zero
    o-def : Clause {[ Str Nat ]} {[]} {Str Nat}
    o-def = record
      { body =
        [ (· ↦ svar o) ]
      }
    def : Definition Δ
    def = record
      { defs =
        [ o ≝ o-def ]
      }
