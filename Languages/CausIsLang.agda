{-# OPTIONS --copatterns --sized-types #-}

{-
In this module, we show that languages are represented by causal stream
functions.

To this end, let A be a non-empty set (the alphabet) and 2 the
Booleans. For a stream s, we denote the list of the first n elements in
s by s ↓ n and by s[n] the element at the n-th position of s.

A function f : Aω → 2ω from streams over A to Boolean streams is
_causal_, if for all natural numbers n : ℕ and streams s,t : Aω, if
s ↓ n = t ↓ n implies that F(s)[n] = F(t)[n]. We denote by
  C(Aω,2ω) = {f : Aω → 2ω | F causal}
the set of all causal stream functions.

A _language_ is a subset of A⋆, the set of finite words over A. Thus the set
of all languages over A is given by the function space A⋆ → 2.

Now we can show that C(Aω,2ω) ≅ A⋆ → 2 by establishing an isomorphism
  α : (A⋆ → 2) → C(Aω,2ω)
with its inverse
  β : C(Aω,2ω) → (A⋆ → 2).

This explains, why the set of languages is the final coalgebra for the
functor F = 2 × (A → Id).
The coinductive extension of a coalgebra c : X → F X is thereby given by
  ĉ : X → C(Aω,2ω)
  (ĉ x s)[0] = c₁ x
  (ĉ x s)'   = ĉ (c₂ x s[0]) s'
where cᵢ = πᵢ ∘ c.
-}

module CausIsLang where

open import Size
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
--  using (_≡_; _≢_; _≗_; refl; module ≡-Reasoning)
open ≡-Reasoning
-- open import Relation.Nullary using (Dec; yes; no)
-- open import Relation.Nullary.Decidable using (⌊_⌋)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; module List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _*_; _≤?_; compare; less; equal; greater)
open import Data.Product using (_×_; _,_; _,′_; proj₁; proj₂)

open import Stream

-- Convenience

∥_∥ : ∀ {a} {A : Set a} → List A → ℕ
∥ l ∥ = length l

_⋆ : Set → Set
A ⋆ = List A

ε : ∀{A} → A ⋆
ε = []

-- Non-empty sets
record NonEmptyS (A : Set) : Set where
  field
    x : A

-- | Causal stream functions
record Causal (A B : Set) : Set where
  field
    F : Stream {∞} A → Stream {∞} B
    .caus : ∀ {n : ℕ} {s t : Stream A} →
            s ↓ n ≡ t ↓ n → (F s) at n ≡ (F t) at n

lang-to-caus : ∀{A} → (A ⋆ → Bool) → (Stream A → Stream Bool)
hd (lang-to-caus L s) = L ε
tl (lang-to-caus L s) = lang-to-caus (λ w → L (hd s ∷ w)) (tl s)

lang-to-caus-explicit : ∀{A} {L : A ⋆ → Bool} {s : Stream A} →
                        (n : ℕ) → (lang-to-caus L s) at n ≡ L(s ↓ n)
lang-to-caus-explicit zero = refl
lang-to-caus-explicit {A} {L} {s} (suc n) =
  begin
    (lang-to-caus L s) at (suc n)
  ≡⟨ refl ⟩
    hd (δ (suc n) (lang-to-caus L s))
  ≡⟨ refl ⟩
    hd (δ n (tl (lang-to-caus L s)))
  ≡⟨ refl ⟩
    hd (δ n (lang-to-caus (λ w → L (hd s ∷ w)) (tl s)))
  ≡⟨ refl ⟩
   (lang-to-caus (λ w → L (hd s ∷ w)) (tl s)) at n
  ≡⟨ lang-to-caus-explicit n ⟩
    (λ w → L (hd s ∷ w))((tl s) ↓ n)
  ≡⟨ refl ⟩
    L (hd s ∷ ((tl s) ↓ n))
  ≡⟨ refl ⟩
    L (s ↓ (suc n))
  ∎

lang-to-caus-is-causal : ∀{A} {L : A ⋆ → Bool} →
                         ∀ {n : ℕ} {s t : Stream A} →
                         s ↓ n ≡ t ↓ n →
                         (lang-to-caus L s) at n ≡ (lang-to-caus L t) at n
lang-to-caus-is-causal {A} {L} {n} {s} {t} p =
  begin
    (lang-to-caus L s) at n
  ≡⟨ lang-to-caus-explicit n ⟩
    L(s ↓ n)
  ≡⟨ cong (λ u → L u) p ⟩
    L(t ↓ n)
  ≡⟨ sym (lang-to-caus-explicit n) ⟩
    (lang-to-caus L t) at n
  ∎

-- Isomorphisms between languages and causal stream transformations

α : ∀{A} → (A ⋆ → Bool) → (Causal A Bool)
α L = record
  { F = lang-to-caus L
  ; caus = lang-to-caus-is-causal
  }

β : ∀{A} {p : NonEmptyS A} → (Causal A Bool) → (A ⋆ → Bool)
β {A} {p} F′ w =
  let open Causal F′
  in F (w ++ˢ repeat (NonEmptyS.x p)) at ∥ w ∥

lemma-restr-extension-to-length-is-id :
  ∀ {A} {s : Stream A} (w : A ⋆) →
  (w ++ˢ s) ↓ ∥ w ∥ ≡ w
lemma-restr-extension-to-length-is-id         []      = refl
lemma-restr-extension-to-length-is-id {A} {s} (a ∷ w) = 
  begin
    ((a ∷ w) ++ˢ s) ↓ ∥ a ∷ w ∥
  ≡⟨ refl ⟩
    ((a ∷ w) ++ˢ s) ↓ (suc ∥ w ∥)
  ≡⟨ refl ⟩
    (hd ((a ∷ w) ++ˢ s)) ∷ ((tl ((a ∷ w) ++ˢ s)) ↓ ∥ w ∥)
  ≡⟨ refl ⟩
    a ∷ ((tl ((a ∷ w) ++ˢ s)) ↓ ∥ w ∥)
  ≡⟨ refl ⟩
    a ∷ ((w ++ˢ s) ↓ ∥ w ∥)
  ≡⟨ cong (λ u → a ∷ u) (lemma-restr-extension-to-length-is-id w) ⟩
    a ∷ w
  ∎

{-
.lemma-β-indep-of-choice : ∀ {A} {F′ : Causal A Bool} {a b : A} {w : A ⋆} →
                     β F′ w ≡ β F′ w
lemma-β-indep-of-choice {A} {F′} {a} {b} {w} =
  let
    open Causal F′
    n = ∥ w ∥
  in begin
    β a F′ w
  ≡⟨ refl ⟩
    F (w ++ˢ repeat a) at n
  ≡⟨ caus {n} {(w ++ˢ repeat a)} {(w ++ˢ repeat b)}
          (trans (lemma-restr-extension-to-length-is-id w)
                 (sym (lemma-restr-extension-to-length-is-id w))) ⟩
    F (w ++ˢ repeat b) at n
  ≡⟨ refl ⟩
    β b F′ w
  ∎
-}

lang-iso-caus→ : ∀{A} {p : NonEmptyS A} {L : A ⋆ → Bool} (w : A ⋆) →
                 β {A} {p} (α L) w ≡ L w
lang-iso-caus→             []      = refl
lang-iso-caus→ {A} {p} {L} (a ∷ w) =
  let
    F′ = α L
    F = Causal.F F′
    n = ∥ w ∥
    x = NonEmptyS.x p
    s = (a ∷ w) ++ˢ repeat x
    K = (λ w → L (hd s ∷ w))
    G′ = α K
    G = Causal.F G′
  in begin
    β F′ (a ∷ w)
  ≡⟨ refl ⟩
    F ((a ∷ w) ++ˢ repeat x) at (suc n)
  ≡⟨ refl ⟩
    F s at (suc n)
  ≡⟨ refl ⟩
    lang-to-caus L s at (suc n)
  ≡⟨ refl ⟩
    hd (δ (suc n) (lang-to-caus L s))
  ≡⟨ refl ⟩
    hd (δ n (tl (lang-to-caus L s)))
  ≡⟨ refl ⟩
    tl (lang-to-caus L s) at n
  ≡⟨ refl ⟩
    lang-to-caus (λ w → L (hd s ∷ w)) (tl s) at n
  ≡⟨ refl ⟩
    G (tl s) at n
  ≡⟨ refl ⟩
    G (w ++ˢ repeat x) at n
  ≡⟨ refl ⟩
    β G′ w
  ≡⟨ refl ⟩
    β (α K) w
  ≡⟨ lang-iso-caus→ w ⟩
    K w
  ≡⟨ refl ⟩
    L (a ∷ w)
  ∎

-- This doesn't work as long as we don't have a notion of causality
-- that does not depend on explicit indexing.
{-
.lang-iso-caus← : ∀{A} {x : A} {F′ : Causal A Bool} (s : Stream A) →
                 Causal.F (α (β x F′)) s ∼ˢ Causal.F F′ s
hd≡ (lang-iso-caus← {A} {x} {F′} s) =
  let
    F = Causal.F F′
    L = β x F′
    G′ = α L
    G = Causal.F G′
  in begin
    hd (G s)
  ≡⟨ refl ⟩
    hd (lang-to-caus L s)
  ≡⟨ refl ⟩
    L ε
  ≡⟨ refl ⟩
    F (ε ++ˢ repeat x) at ∥ ε {A} ∥
  ≡⟨ refl ⟩
    F (repeat x) at 0
  ≡⟨ refl ⟩
    F (repeat x) at 0
  ≡⟨ Causal.caus F′ {0} {repeat x} {s} refl ⟩
    F s at 0
  ≡⟨ refl ⟩
    hd (F s)
  ∎

tl∼ (lang-iso-caus← {A} {x} {F′} s) =
  let
    F = Causal.F F′
    L = β x F′
    G′ = α L
    G = Causal.F G′
    K = (λ w → L (hd s ∷ w))
  in beginˢ
    tl (G s)
  ∼ˢ⟨ s-bisim-refl ⟩
    tl (lang-to-caus L s)
  ∼ˢ⟨ s-bisim-refl ⟩
    lang-to-caus (λ w → L (hd s ∷ w)) (tl s)
  ∼ˢ⟨ s-bisim-refl ⟩
    lang-to-caus K (tl s)
  ∼ˢ⟨ s-bisim-refl ⟩
    Causal.F (α K) (tl s)
  ∼ˢ⟨ {!!} ⟩
    tl (F s)
  ∎ˢ
-}

lemma-length-restr : ∀ {A} {s : Stream A} (n : ℕ) → ∥ (s ↓ n) ∥ ≡ n
lemma-length-restr         zero    = refl
lemma-length-restr {A} {s} (suc n) =
  begin
    ∥ (s ↓ (suc n)) ∥
  ≡⟨ refl ⟩
    ∥ hd s ∷ ((tl s) ↓ n) ∥
  ≡⟨ refl ⟩
    suc ∥ (tl s) ↓ n ∥
  ≡⟨ cong (λ u → suc u) (lemma-length-restr n) ⟩
    suc n
  ∎

.lang-iso-caus← : ∀{A} {p : NonEmptyS A} {F′ : Causal A Bool} {s : Stream A}
                  (n : ℕ) → Causal.F (α (β F′)) s at n ≡ Causal.F F′ s at n
lang-iso-caus← {A} {p} {F′} {s} n =
  let
    F = Causal.F F′
    L = β F′
  in begin
    Causal.F (α L) s at n
  ≡⟨ refl ⟩
    lang-to-caus L s at n
  ≡⟨ lang-to-caus-explicit n ⟩
    L (s ↓ n)
  ≡⟨ refl ⟩
    F ((s ↓ n) ++ˢ repeat x) at ∥ s ↓ n ∥
  ≡⟨ Causal.caus F′ {∥ s ↓ n ∥} {(s ↓ n) ++ˢ repeat x} {s} lemma-restr-ext ⟩
    F s at  ∥ (s ↓ n) ∥
  ≡⟨ cong (λ u → F s at u) (lemma-length-restr n) ⟩
    F s at n
  ∎
  where
    x = NonEmptyS.x p

    lemma-restr-ext : ((s ↓ n) ++ˢ repeat x) ↓ ∥ s ↓ n ∥ ≡ s ↓ ∥ s ↓ n ∥
    lemma-restr-ext =
      begin
        ((s ↓ n) ++ˢ repeat x) ↓ ∥ s ↓ n ∥
      ≡⟨ lemma-restr-extension-to-length-is-id (s ↓ n) ⟩
        s ↓ n
      ≡⟨ cong (λ u → s ↓ u) (sym (lemma-length-restr n)) ⟩
        s ↓ ∥ s ↓ n ∥
      ∎
