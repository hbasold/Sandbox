-- | Examples for SDE.

module SDE-Example where

open import Size
import Level
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open ≡-Reasoning

open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Product as Prod renaming (Σ to ⨿)
open import Data.Nat as Nat
open import Data.Sum as Sum
open import Data.Fin hiding (_+_)

open import Streams
open import SDE

-- Example: Basic operations over streams over naturals
[_] : ∀{i} → ℕ → Stream {i} ℕ
hd [ n ] = n
tl [ n ] = [ 0 ]

_⊕_ : ∀ {i} → Stream {i} ℕ → Stream {i} ℕ → Stream {i} ℕ
hd (x ⊕ y) = hd x + hd y
tl (x ⊕ y) = tl x ⊕ tl y

_⊗_ : ∀{i} → Stream {i} ℕ → Stream {i} ℕ → Stream {i} ℕ
hd (x ⊗ y)           = hd x * hd y
tl (_⊗_ {i} x y) {j} = (tl x ⊗ y) ⊕ ([ hd x ] ⊗ (tl y))


--------- Example for syntactic SDE.
-- We define symbols iₙ (n ∈ ℕ), p and c through SDEs for streams
-- over natural numbers. Here, iₙ is the injection of the number n into streams
-- and corresponds to [n], p is stream addition, and c is the convolution
-- product. The SDEs are the usual ones:
-- (iₙ)(0) = n
-- (iₙ)'   = i₀
-- (p s t)(0) = s(0) + t(0)
-- (p s t)'   = p s' t'
-- (c s t)(0) = s(0) * t(0)
-- (c s t)'   = p (c s' t) (c i_{s(0)} t')

-- First, we define the signature, which has ℕ-many symbols for the iₙ of
-- arity 0 and two symbols (p and c) of arity 2.
Σ : Sig
Σ = record { ∥_∥ = ℕ ⊎ Fin 2 ; ar = ar-Σ }
  where
    ar-Σ : ℕ ⊎ Fin 2 → Set
    ar-Σ (inj₁ _)       = Fin 0
    ar-Σ (inj₂ zero)    = Fin 2
    ar-Σ (inj₂ (suc _)) = Fin 2

-- Short-hand notations for the symbols.

-- | Injections iₙ
i : ℕ → ∥ Σ ∥
i n = inj₁ n

-- | Plus
p : ∥ Σ ∥
p = inj₂ (# 0)

-- | Convolution product
c : ∥ Σ ∥
c = inj₂ (# 1)

-- | We are going to define the SDEs by means of two variabls, later called x
-- and y.
X : Set
X = Fin 2

open Terms Σ public
open SDE-Impl Σ X public

-- | Short-hand names for variables and the variables denoting the corresponding
-- derivatives.
x y x' y' : V
x = inj₁ (# 0)
y = inj₁ (# 1)
x' = inj₂ (# 0)
y' = inj₂ (# 1)

-- Term constructors
i₁ : ℕ → T V
i₁ n = sup (inj₁ (i n , (λ ())))

p₁ : T V → T V → T V
p₁ t s = sup (inj₁ (p , α))
   where
     α : Fin 2 → T V
     α zero    = t
     α (suc _) = s

c₁ : T V → T V → T V
c₁ t s = sup (inj₁ (c , α))
   where
     α : Fin 2 → T V
     α zero    = t
     α (suc _) = s

-- | SDEs describing iₙ, ⊕ and ⊗
E : SDE ℕ
E (inj₁ n) = (λ _ → n) , (λ _ → sup (inj₁ (i 0 , (λ ()))))
E (inj₂ zero) = out , step
  where
    out : (Fin 2 → ℕ) → ℕ
    out r = r (# 0) + r (# 1)

    step : (Fin 2 → ℕ) → T V
    step _ = p₁ (η x') (η y')
E (inj₂ (suc _)) = out , step
  where
    out : (Fin 2 → ℕ) → ℕ
    out r = r (# 0) * r (# 1)

    step : (Fin 2 → ℕ) → T V
    step o = p₁
             (c₁ (η x') (η y))
             (c₁ (i₁ (o (# 0))) (η y'))

-- | Assignment of variables to positions of the symbols of our SDEs
vars : (f : ∥ Σ ∥) → ar Σ f → X
vars (inj₁ x)       ()
vars (inj₂ zero)    x = x
vars (inj₂ (suc _)) x = x

-- | Standard variable assignment.
put : ∀ {i} → Stream {i} ℕ → Stream {i} ℕ → (X → Stream {i} ℕ)
put s t zero    = s
put s t (suc _) = t

-- | Dummy stream for unused variables
dummy : Stream ℕ
hd dummy = 0
tl dummy = dummy

-- | Define injection [_] from SDE
[_]' : ℕ → Stream ℕ
[ n ]' = ⟦ E ⟧ vars (i n) (put dummy dummy)

-- | The addition of the streams s and t can be given by the interpretation
-- of the symbol p of the SDE above with variable assignment (x ↦ s, y ↦ t).
_⊕'_ : ∀ {i} → Stream {i} ℕ → Stream {i} ℕ → Stream {i} ℕ
s ⊕' t = ⟦ E ⟧ vars p (put s t)

_⊗'_ : ∀ {i} → Stream {i} ℕ → Stream {i} ℕ → Stream {i} ℕ
s ⊗' t = ⟦ E ⟧ vars c (put s t)

------ Correctness for the examples

-- We cheat a bit for now
postulate
  ext : Extensionality Level.zero Level.zero

-- | The interpretation of the SDE for stream addition has indeed the
-- same behaviour as the direct implemenentation.
correct-⊕ : ∀ {s t} → (s ⊕ t) ∼ˢ (s ⊕' t)
correct-⊕ = lem
  where
    lem₁ : ∀{x y} (z : X) → tl (put x y z) ≡ put (tl x) (tl y) z
    lem₁ zero = refl
    lem₁ (suc z) = refl

    -- Bisimulation relating s ⊕ t and the interpretation of p with
    -- variable assignment (x ↦ s, y ↦ t).
    R : Rel (Stream ℕ) _
    R x y = ∃ (λ s → ∃ (λ t → x ≡ s ⊕ t × y ≡ ⟦ E ⟧ vars p (put s t)))

    is-bisim : is-Bisim R
    is-bisim x y (s , t , x=⊕ , y=E) = hd-≡ , tl-R
      where
        hd-≡ : hd x ≡ hd y
        hd-≡ =
          begin
            hd x
          ≡⟨ cong hd x=⊕ ⟩
            hd (s ⊕ t)
          ≡⟨ refl ⟩
            hd (⟦ E ⟧ vars p (put s t))
          ≡⟨ cong hd (sym y=E) ⟩
            hd y
          ∎

        tl-R : R (tl x) (tl y)
        tl-R = (tl s , tl t , u' , v)
          where
            u' : tl x ≡ tl s ⊕ tl t
            u' =
              begin
                tl x
              ≡⟨ cong (λ x → tl x {∞}) x=⊕ ⟩
                tl (s ⊕ t)
              ≡⟨ refl ⟩
                tl s ⊕ tl t
              ∎

            -- This uses, for now, extensionality
            v : tl y ≡ ⟦ E ⟧ vars p (put (tl s) (tl t))
            v =
              begin
                tl y
              ≡⟨ cong (λ x₁ → tl x₁ {∞}) y=E ⟩
                tl (⟦ E ⟧ vars p (put s t))
              ≡⟨ refl ⟩
                ⟦ E ⟧₁ vars (p₁ (sup (inj₂ x')) (sup (inj₂ y'))) (put s t)
              ≡⟨ refl ⟩
                ⟦ E ⟧ vars p (λ x → tl ((put s t) x))
              ≡⟨ cong (⟦ E ⟧ vars p) (ext lem₁) ⟩
                ⟦ E ⟧ vars p (put (tl s) (tl t))
              ∎

    lem : ∀{s t} → (s ⊕ t) ∼ˢ (⟦ E ⟧ vars p (put s t))
    lem {s} {t} = ex-bisimulation→bisim is-bisim rel
      where
        rel : R (s ⊕ t) (⟦ E ⟧ vars p (put s t))
        rel = (s , t , refl , refl)

-- Conjecture.
correct-⊗ : ∀ {s t} → (s ⊗ t) ∼ˢ (s ⊗' t)
correct-⊗ = {!!}
