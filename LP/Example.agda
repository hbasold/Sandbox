module Example where

import Level
open import Signature
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Product as Prod renaming (Σ to ⨿)
open import Data.Sum as Sum
open import Relation.Nullary
open import Relation.Unary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

postulate
  ext : Extensionality Level.zero Level.zero


------
-- Examples
-----

module NatProg where
  Σ : Sig
  ∥ Σ ∥ = Fin 3
  ar Σ zero                         = Fin 0 -- 0
  ar Σ (suc zero)                   = Fin 1 -- succ
  ar Σ (suc (suc _))                = Fin 1 -- nat

  open import Terms Σ
  V = ℕ
  Z S N : ∥ Σ ∥
  Z     = # 0
  S     = # 1
  N     = # 2

  z : T V
  z = μ (ι (Z , (λ ())))

  s nat : T V → T V
  s   t = μ (ι (S , (λ _ → t)))
  nat t = μ (ι (N , (λ _ → t)))


  z∞ : T∞ V
  z∞ = χ z

  s∞ nat∞ : ∀{X} → T∞ X → T∞ X
  s∞   t = μ∞ (ι∞ (S , (λ _ → t)))
  nat∞ t = μ∞ (ι∞ (N , (λ _ → t)))

  inf : T∞ ⊥
  inf = corec (λ x → inj₁ (S , (λ _ → tt))) tt

  inf-nat : T∞ ⊥
  inf-nat = nat∞ inf

  open import Program Σ V

  -- | Program consisting of
  -- ⇒ nat(0)
  -- nat(n) ⇒ nat(s n)
  P : Program
  P = ((0 , (λ ())) , ( , clauses))
    where
      clauses : Fin 2 → Clause
      clauses zero             = (0 , (λ ())) ⊢ nat z
      clauses (suc _)          = (1 , b)      ⊢ nat (s n)
        where
          n = η 0

          b : Fin 1 → T V
          b _ = nat n

  open import Herbrand Σ V P

  lem : ¬ (∃ λ σ → (inf ~ app∞ σ (χ (geth-ν P (# 0)))))
  lem (σ , p) with out~ p
  lem (σ , p) | () , _

  bad-ν : inf-nat ∈ Herbrand-ν
  bw-closed bad-ν = inj₁ p
    where
      p : (i : dom-ν P) {σ : V → T∞ ⊥} →
          inf-nat ~ (app∞ σ (χ (geth-ν P i))) →
          (j : dom (getb-ν P i)) →
          app∞ σ (χ (get (getb-ν P i) j)) ∈ Herbrand-ν

{-
      p i {σ} p j with out inf-nat | out (σ 0) | out~ p
      p i p j | inj₁ (zero , α) | v | r = {!!}
      p i p j | inj₁ (suc zero , α) | v | r = {!!}
      p i p j | inj₁ (suc (suc _) , α) | v | r = {!!}
      p i p j | inj₂ () | v | r
-}
      p i {σ} p j with out (σ 0) | out~ p
      p zero p () | u | refl , r
      p (suc i) p zero | inj₁ (zero , _) | refl , r = {!!}
      p (suc i) p zero | inj₁ (suc zero , _) | refl , r = {!!}
      p (suc i) p zero | inj₁ (suc (suc _) , proj₂) | refl , r = {!!}
      p (suc i) p zero | inj₂ () | refl , r
      p (suc _) p (suc ()) | u | refl , r

    {-
      f : ?
      f i {σ} p j with out~ p
      ... | u = ?
-}
  bad : inf-nat ∈ Herbrand-μ
  bad = coind-μ bad-ν

{-

module BitList where
  Σ : Sig
  ∥ Σ ∥ = Fin 6
  ar Σ zero                            = Fin 0 -- 0
  ar Σ (suc zero)                      = Fin 0 -- 1
  ar Σ (suc (suc zero))                = Fin 1 -- bit(x)
  ar Σ (suc (suc (suc zero)))          = Fin 1 -- blist(x)
  ar Σ (suc (suc (suc (suc zero))))    = Fin 0 -- nil
  ar Σ (suc (suc (suc (suc (suc f))))) = Fin 2 -- cons(x,y)

  open import Terms Σ
  V = ℕ

  Z O Bit BList Nil Cons : ∥ Σ ∥
  Z     = # 0
  O     = # 1
  Bit   = # 2
  BList = # 3
  Nil   = # 4
  Cons  = # 5

  z o nil : T V
  z   = μ (ι (Z , (λ ())))
  o   = μ (ι (O , (λ ())))
  nil = μ (ι (Nil , (λ ())))

  bit blist : T V → T V
  bit   t = μ (ι (Bit , (λ _ → t)))
  blist t = μ (ι (BList , (λ _ → t)))

  bin-branch : {X : Set} → X → X → Fin 2 → X
  bin-branch x y zero    = x
  bin-branch x y (suc _) = y

  cons-br-distr : ∀{X Y} (t s : X) (f : X → Y) →
                  f ∘ bin-branch t s ≡ bin-branch (f t) (f s)
  cons-br-distr t s f = ext p
    where
      p : (i : Fin 2) → f (bin-branch t s i) ≡ bin-branch (f t) (f s) i
      p zero    = refl
      p (suc _) = refl

  cons : T V → T V → T V
  cons t s = μ (ι (Cons , bin-branch t s))

  bit0 bit1 : T V
  bit0 = bit z
  bit1 = bit o

  open import Program Σ V

  -- | Program consisting of
  -- ⇒ bit(0)
  -- ⇒ bit(1)
  -- ⇒ blist(nil)
  -- bit(x), blist(y) ⇒ blist(cons(x,y))
  P : Program
  P = , clauses
    where
      clauses : Fin 4 → Clause
      clauses zero                = (0 , (λ ())) ⊢ bit0
      clauses (suc zero)          = (0 , (λ ())) ⊢ bit1
      clauses (suc (suc zero))    = (0 , (λ ())) ⊢ nil
      clauses (suc (suc (suc c))) = (2 , b)      ⊢ blist (cons (η 0) (η 1))
        where
          b : Fin 2 → T V
          b zero = bit (η 0)
          b (suc i) = blist (η 1)

  open import Rewrite Σ V P

  X S bitX : T V
  X = η 0
  S = blist (cons X (cons X nil))
  bitX = bit X

  bitX-val : Val bitX
  bitX-val zero                ()      x
  bitX-val (suc zero)          ()      x
  bitX-val (suc (suc zero))    ()      x
  bitX-val (suc (suc (suc _))) zero    ()
  bitX-val (suc (suc (suc _))) (suc _) ()

  step1 : S ⟿ bitX
  step1 = rew-step (# 3) (# 0) {σ} σ-match
    where
      σ : Subst V V
      σ zero = X
      σ (suc zero) = cons X nil
      σ (suc (suc n)) = η (suc (suc n))

      σ-match : matches (geth P (# 3)) S σ
      σ-match =
        begin
          app σ (blist (cons X (η 1)))
        ≡⟨ refl ⟩
          μ (T₁ σ (blist (cons X (η 1))))
        ≡⟨ refl ⟩
          μ (T₁ σ (μ (ι (BList , (λ _ → (cons X (η 1)))))))
        ≡⟨ refl ⟩
          μ (μ (ι (BList , (λ _ → T₁ σ (cons X (η 1))))))
        ≡⟨ refl ⟩
          μ (μ (ι (BList , (λ _ → T₁ σ (μ (ι (Cons , bin-branch X (η 1))))))))
        ≡⟨ refl ⟩
          μ (μ (ι (BList , (λ _ → μ (ι (Cons , T₁ σ ∘ (bin-branch X (η 1))))))))
        ≡⟨ cong (λ u → μ (μ (ι (BList , (λ _ → μ (ι (Cons , u)))))))
                (cons-br-distr X (η 1) (T₁ σ)) ⟩
          μ (μ (ι (BList , (λ _ →
               μ (ι (Cons , (bin-branch (T₁ σ X) (T₁ σ (η 1)))))))))
        ≡⟨ refl ⟩
          μ (μ (ι (BList , (λ _ →
               μ (ι (Cons , (bin-branch (η (σ 0)) (η (σ 1)))))))))
        ≡⟨ cong (λ u → μ (μ (ι (BList , (λ _ → μ (ι (Cons , u)))))))
                (sym (cons-br-distr (σ 0) (σ 1) η)) ⟩
          μ (μ (ι (BList , (λ _ →
               μ (ι (Cons , (η ∘ (bin-branch (σ 0) (σ 1)))))))))
        ≡⟨ refl ⟩
          blist (cons (σ 0) (σ 1))
        ≡⟨ refl ⟩
          blist (cons X (cons X nil))
        ≡⟨ refl ⟩
          S
        ∎

  term1 : S ↓ bitX
  term1 = step bitX bitX (val bitX-val) step1

  -- Problem: The substitution needs to match _all_ leaves!!!
-}
