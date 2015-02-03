module Terms where

import Level
open import Data.Unit as Unit
open import Data.List as List
open import Data.Product as Product
open import Categories.Category using (Category)

data Type : Set where
  Nat : Type
  _ˢ : Type → Type
  _⇒_ : Type → Type → Type

infixr 5 _⇒_

open import Common.Context Type
  using (Ctx; Var; zero; ctx-cat; ctx-bin-coproducts)
  renaming (succ to succ)
open Categories.Category.Category ctx-cat
  renaming ( _⇒_ to _▹_
           ; _≡_ to _≈_
           ; _∘_ to _●_
           ; id  to ctx-id
           )
open import Categories.Object.BinaryCoproducts ctx-cat
open BinaryCoproducts ctx-bin-coproducts

data Term (Γ : Ctx) : (σ : Type) → Set where
  var  : ∀{σ : Type}       (x : Var Γ σ)          → Term Γ σ
  abs  : ∀{σ τ : Type}     (t : Term (σ ∷ Γ) τ)   → Term Γ (σ ⇒ τ)
  app  : ∀{σ τ : Type}     (t : Term Γ (σ ⇒ τ))
                           (s : Term Γ σ)         → Term Γ τ
  -- Constants for recursion over ℕ
  𝟘    : Term Γ Nat
  s⁺   : Term Γ (Nat ⇒ Nat)
  R    : ∀{σ : Type} → Term Γ (σ ⇒ (Nat ⇒ σ ⇒ σ) ⇒ Nat ⇒ σ)
  -- Constants for corecursion over streams
  hd   : ∀{σ : Type} → Term Γ (σ ˢ ⇒ σ)
  tl   : ∀{σ : Type} → Term Γ (σ ˢ ⇒ σ ˢ)
  C    : ∀{σ τ : Type} → Term Γ ((σ ⇒ τ) ⇒ (σ ⇒ σ) ⇒ σ ⇒ τ ˢ)

-- Improve readability
_⟨$⟩_ : ∀{Γ σ τ} (t : Term Γ (σ ⇒ τ)) (s : Term Γ σ) → Term Γ τ
t ⟨$⟩ s = app t s

infixl 0 _⟨$⟩_

hd′ : ∀{Γ σ} → Term Γ (σ ˢ) → Term Γ σ
hd′ s = hd ⟨$⟩ s

tl′ : ∀{Γ σ} → Term Γ (σ ˢ) → Term Γ (σ ˢ)
tl′ s = tl ⟨$⟩ s

C′ : ∀{Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ (σ ⇒ σ) → Term Γ (σ ⇒ τ ˢ)
C′ h t = (C ⟨$⟩ h) ⟨$⟩ t

R′ : ∀{Γ σ} → Term Γ σ → Term Γ (Nat ⇒ σ ⇒ σ) → Term Γ (Nat ⇒ σ)
R′ x f = R ⟨$⟩ x ⟨$⟩ f

ƛ : ∀{Γ σ τ} → (Var (σ ∷ Γ) σ → Term (σ ∷ Γ) τ) → Term Γ (σ ⇒ τ)
ƛ f = abs (f zero)

abs₁ : ∀{Γ τ σ} →
       (Term (τ ∷ Γ) τ → Term (τ ∷ Γ) σ)
       → Term Γ (τ ⇒ σ)
abs₁ f = abs (f (var zero))

abs₂ : ∀{Γ τ₁ τ₂ σ} →
       (Term (τ₂ ∷ τ₁ ∷ Γ) τ₁ →
         Term (τ₂ ∷ τ₁ ∷ Γ) τ₂ →
         Term (τ₂ ∷ τ₁ ∷ Γ) σ) →
       Term Γ (τ₁ ⇒ τ₂ ⇒ σ)
abs₂ {Γ} {τ₁} f = abs (abs (f x₁ x₂))
  where
    x₁ = var (succ τ₁ zero)
    x₂ = var zero

abs₃ : ∀{Γ τ₁ τ₂ τ₃ σ} →
       (Term (τ₃ ∷ τ₂ ∷ τ₁ ∷ Γ) τ₁ →
         Term (τ₃ ∷ τ₂ ∷ τ₁ ∷ Γ) τ₂ →
         Term (τ₃ ∷ τ₂ ∷ τ₁ ∷ Γ) τ₃ →
         Term (τ₃ ∷ τ₂ ∷ τ₁ ∷ Γ) σ) →
       Term Γ (τ₁ ⇒ τ₂ ⇒ τ₃ ⇒ σ)
abs₃ {Γ} {τ₁} {τ₂} f = abs (abs (abs (f x₁ x₂ x₃)))
  where
    x₁ = var (succ τ₁ (succ τ₁ zero))
    x₂ = var (succ τ₂ zero)
    x₃ = var zero


--------------------------------------
---- Examples ---

π₁ :  ∀{Γ σ τ} → Term Γ (σ ⇒ τ ⇒ σ)
π₁ = abs₂ (λ x₁ x₂ → x₁)

π₂ :  ∀{Γ σ τ} → Term Γ (σ ⇒ τ ⇒ τ)
π₂ = abs₂ (λ x₁ x₂ → x₂)

-- | Prepend element to a stream
-- hd (cons x s) = x
-- tl (cons x s) = s
-- This needs to use continuations.
conc : ∀{Γ σ} → Term Γ (σ ⇒ σ ˢ ⇒ σ ˢ)
conc {Γ} {σ} = abs (abs (C′ f g ⟨$⟩ i))
  where
    -- | State space
    S = (σ ⇒ σ ˢ ⇒ σ) ⇒ σ
    -- | local context
    Γ′ = σ ˢ ∷ σ ∷ Γ

    f : Term Γ′ (S ⇒ σ)
    f = abs₁ (λ v → v ⟨$⟩ π₁)

    g : Term Γ′ (S ⇒ S)
    g = abs₂ (λ v _h →
             v ⟨$⟩ (abs₂ (λ _ s →
               h ⟨$⟩ (hd′ s) ⟨$⟩ (tl′ s))
             )
        )
      where
        Γ′′ = σ ˢ ∷ σ ∷ (σ ⇒ σ ˢ ⇒ σ) ∷ S ∷ Γ′
        h : Term Γ′′ (σ ⇒ σ ˢ ⇒ σ)
        h = var (succ (σ ⇒ σ ˢ ⇒ σ) (succ (σ ⇒ σ ˢ ⇒ σ) zero))

    i : Term Γ′ S
    i = abs₁ (λ h → h ⟨$⟩ x ⟨$⟩ s)
      where
        s : Term ((σ ⇒ σ ˢ ⇒ σ) ∷ Γ′) (σ ˢ)
        s = var (succ (σ ˢ) zero)
        x : Term ((σ ⇒ σ ˢ ⇒ σ) ∷ Γ′) σ
        x = var (succ σ (succ σ zero))

_∺_ : ∀{Γ σ} → Term Γ σ → Term Γ (σ ˢ) → Term Γ (σ ˢ)
x ∺ s = conc ⟨$⟩ x ⟨$⟩ s

id′ : ∀{Γ σ} → Term Γ (σ ⇒ σ)
id′ = abs₁ (λ x → x)

repeat : ∀{Γ σ} → Term Γ (σ ⇒ σ ˢ)
repeat = C′ id′ id′

-- | Extend a stream that is defined up to n by an element on the right, i.e.,
--     ext x 0     s  = repeat x
-- hd (ext x (n+1) s) = hd s
-- tl (ext x (n+1) s) = ext x n (tl s)
-- Thus ext is given by a recursion, followed by a corecursion:
-- ext x = R (λ_. repeat x) f
-- f _ h s = hd s ∷ (h (tl s))
ext : ∀{Γ σ} → Term Γ (σ ⇒ Nat ⇒ σ ˢ ⇒ σ ˢ)
ext {Γ} {σ} = abs (R′ (abs (repeat ⟨$⟩ x)) f)
  where
    Γ′ = σ ∷ Γ
    x : Term (σ ˢ ∷ Γ′) σ
    x = var (succ σ zero)

    f : Term Γ′ (Nat ⇒ (σ ˢ ⇒ σ ˢ) ⇒ σ ˢ ⇒ σ ˢ)
    f = abs₃ (λ _ h s → (hd′ s) ∺ (h ⟨$⟩ (tl′ s)))
