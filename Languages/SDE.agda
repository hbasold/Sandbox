{-# OPTIONS --copatterns --sized-types #-}

open import Size
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
open ≡-Reasoning

open import Algebra.Structures using (IsCommutativeSemiring; IsCommutativeMonoid)

open import Data.Nat
open import Data.Nat.Properties using (isCommutativeSemiring)
open import Stream
open ∼ˢ∞-Reasoning

⟦_⟧ : ℕ → Str ℕ
hd (⟦ n ⟧) = n
tl (⟦ n ⟧) = ⟦ 0 ⟧

_⊕_ : ∀{i} → Str {i} ℕ → Str {i} ℕ → Str {i} ℕ
hd (s ⊕ t) = (hd s) + (hd t)
tl (s ⊕ t) = (tl s) ⊕ (tl t)

_×_ : ∀{i} → Str {i} ℕ → Str {i} ℕ → Str {i} ℕ
hd (s × t) = hd s * hd t
tl (s × t)= ((tl s) × t) ⊕ (⟦ hd s ⟧ × (tl t))

comm-* : ∀ m n → m * n ≡ n * m
comm-* = IsCommutativeMonoid.comm
         (IsCommutativeSemiring.*-isCommutativeMonoid isCommutativeSemiring)

comm-+ : ∀ m n → m + n ≡ n + m
comm-+ = IsCommutativeMonoid.comm
         (IsCommutativeSemiring.+-isCommutativeMonoid isCommutativeSemiring)

Bisim = _∼ˢ_

{-
mutual
  comm-× : ∀{i} →
           (s t : Str {i} ℕ) → Bisim {ℕ} {i} (s × t) (t × s)
  hd≡ (comm-× s t) = comm-* (hd s) (hd t)
  tl∼ (comm-× s t) = lem-comm-× s t

  lem-comm-× : ∀{i} → ∀{j : Size< i} →
               (s t : Str {i} ℕ) →
               Bisim {ℕ} {j}
                 ((tl s × t) ⊕ (⟦ hd s ⟧ × tl t))
                 ((tl t × s) ⊕ (⟦ hd t ⟧ × tl s))
  hd≡ (lem-comm-× {i} {j} s t) =
    begin
      hd s' * hd t + hd s * hd t'
    ≡⟨ comm-+ (hd s' * hd t) (hd s * hd t') ⟩
      hd s * hd t' + hd s' * hd t
    ≡⟨ cong (λ x → x + hd s' * hd t) (comm-* (hd s) (hd t')) ⟩
      hd t' * hd s + hd s' * hd t
    ≡⟨ cong (λ x → hd t' * hd s + x) (comm-* (hd s') (hd t)) ⟩
      hd t' * hd s + hd t * hd s'
    ∎
    where
      s' = tl s {j}
      t' = tl t {j}

  tl∼ (lem-comm-× {i} {j} s t) {k} = lem {k}
    where
      s' = tl s {j}
      t' = tl t {j}

      lem : ∀{k : Size< j} → Bisim {ℕ} {k}
        (((tl s' × t) ⊕ (⟦ hd s' ⟧ × t')) ⊕ ((⟦ 0 ⟧ × t') ⊕ (⟦ hd s ⟧ × tl t')))
        (((tl t' × s) ⊕ (⟦ hd t' ⟧ × s')) ⊕ ((⟦ 0 ⟧ × s') ⊕ (⟦ hd t ⟧ × tl s')))
      lem = {!!}
        where
          s'' = tl s' {k}
          t'' = tl t' {k}
-}

zero-⊕-unit-l : (s : Str ℕ) → (⟦ 0 ⟧ ⊕ s) ∼ˢ∞ s
hd≡∞ (zero-⊕-unit-l s) = refl
tl∼∞ (zero-⊕-unit-l s) = zero-⊕-unit-l (tl s)

zero-⊕-unit-r : (s : Str ℕ) → (s ⊕ ⟦ 0 ⟧) ∼ˢ∞ s
hd≡∞ (zero-⊕-unit-r s) = comm-+ (hd s) 0
tl∼∞ (zero-⊕-unit-r s) = zero-⊕-unit-r (tl s)

zero-×-annihil-l : (s : Str ℕ) → (⟦ 0 ⟧ × s) ∼ˢ∞ ⟦ 0 ⟧
hd≡∞ (zero-×-annihil-l s) = refl
tl∼∞ (zero-×-annihil-l s) =
  beginˢ∞
    tl (⟦ 0 ⟧ × s)
  ∼ˢ∞⟨ s-bisim∞-refl ⟩
    (⟦ 0 ⟧ × s) ⊕ (⟦ 0 ⟧ × tl s)
  ∼ˢ∞⟨ {!!} ⟩
    tl (⟦ 0 ⟧)
  ∎ˢ∞

mutual
  comm-× : (s t : Str ℕ) → (s × t) ∼ˢ∞ (t × s)
  hd≡∞ (comm-× s t) = comm-* (hd s) (hd t)
  tl∼∞ (comm-× s t) = lem-comm-× s t

  lem-comm-× : (s t : Str ℕ) →
               ((tl s × t) ⊕ (⟦ hd s ⟧ × tl t))
               ∼ˢ∞ ((tl t × s) ⊕ (⟦ hd t ⟧ × tl s))
  hd≡∞ (lem-comm-× s t) =
    begin
      hd s' * hd t + hd s * hd t'
    ≡⟨ comm-+ (hd s' * hd t) (hd s * hd t') ⟩
      hd s * hd t' + hd s' * hd t
    ≡⟨ cong (λ x → x + hd s' * hd t) (comm-* (hd s) (hd t')) ⟩
      hd t' * hd s + hd s' * hd t
    ≡⟨ cong (λ x → hd t' * hd s + x) (comm-* (hd s') (hd t)) ⟩
      hd t' * hd s + hd t * hd s'
    ∎
    where
      s' = tl s
      t' = tl t

  tl∼∞ (lem-comm-× s t) = lem
    where
      s' = tl s
      t' = tl t

      lem :
        (((tl s' × t) ⊕ (⟦ hd s' ⟧ × t')) ⊕ ((⟦ 0 ⟧ × t') ⊕ (⟦ hd s ⟧ × tl t')))
        ∼ˢ∞ (((tl t' × s) ⊕ (⟦ hd t' ⟧ × s')) ⊕ ((⟦ 0 ⟧ × s') ⊕ (⟦ hd t ⟧ × tl s')))
      lem = {!!}
        where
          s'' = tl s'
          t'' = tl t'
