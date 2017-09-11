module StreamEnc where

open import Data.Unit hiding (_≤_)
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality as P
open ≡-Reasoning

≤-step : ∀{k n} → k ≤ n → k ≤ suc n
≤-step z≤n = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

pred-≤ : ∀{k n} → suc k ≤ n → k ≤ n
pred-≤ (s≤s p) = ≤-step p

Str : Set → Set
Str A = ℕ → A

hd : ∀{A} → Str A → A
hd s = s 0

tl : ∀{A} → Str A → Str A
tl s n = s (suc n)

_ω : ∀{A} → A → Str A
(a ω) n = a

_∷_ : ∀{A} → A → Str A → Str A
(a ∷ s) 0       = a
(a ∷ s) (suc n) = s n

module Mealy (A B : Set) where

  M : Set → Set
  M X = A → B × X

  M₁ : {X Y : Set} → (X → Y) → M X → M Y
  M₁ f g a =
    let (b , x) = g a
    in (b , f x)

  𝓜 : Set
  𝓜 = Str A → Str B

  d : 𝓜 → M 𝓜
  d f a = (f (a ω) 0 , (λ s n → f (a ∷ s) (suc n)))

  corec : ∀{X} → (c : X → M X) → X → 𝓜
  corec c x s zero    = proj₁ (c x (hd s))
  corec c x s (suc n) = corec c (proj₂ (c x (hd s))) (tl s) n

  compute' : ∀{X} (c : X → M X) (x : X) →
            ∀ a → d (corec c x) a ≡ M₁ (corec c) (c x) a
  compute' c x a =
    begin
      d (corec c x) a
    ≡⟨ refl ⟩
      ((corec c x) (a ω) 0 , λ s n → (corec c x) (a ∷ s) (suc n))
    ≡⟨ refl ⟩
      (proj₁ (c x (hd (a ω)))
      , λ s n → corec c (proj₂ (c x (hd (a ∷ s)))) (tl (a ∷ s)) n)
    ≡⟨ refl ⟩
      (proj₁ (c x a) , λ s n → corec c (proj₂ (c x a)) (λ n → s n) n)
    ≡⟨ refl ⟩
      (proj₁ (c x a) , λ s n → corec c (proj₂ (c x a)) s n)
    ≡⟨ refl ⟩
      (proj₁ (c x a) , λ s → corec c (proj₂ (c x a)) s)
    ≡⟨ refl ⟩
      (proj₁ (c x a) , corec c (proj₂ (c x a)))
    ≡⟨ refl ⟩
      M₁ (corec c) (c x) a
    ∎

  compute : ∀{X} (c : X → M X) (x : X) →
            d (corec c x) ≡ M₁ (corec c) (c x)
  compute c x =
    begin
      d (corec c x)
    ≡⟨ refl ⟩
      (λ a → d (corec c x) a)
    ≡⟨ refl ⟩ -- Same as in compute'
      (λ a → M₁ (corec c) (c x) a)
    ≡⟨ refl ⟩
      M₁ (corec c) (c x)
    ∎

module MealyT (A B : Set) (a₀ : A) where

  M : Set → Set
  M X = ⊤ ⊎ (A → B × X)

  M₁ : {X Y : Set} → (X → Y) → M X → M Y
  M₁ f (inj₁ x) = inj₁ x
  M₁ f (inj₂ g) =
    inj₂ (λ a →
      let (b , x) = g a
      in (b , f x))

  Mono : (Str A → Str (⊤ ⊎ B)) → Set
  -- Mono f = ∀ n → (∃ λ s → ∃ λ b → f s n ≡ inj₂ b) →
  --                ∀ s → ∀ k → k ≤ n → (∃ λ b → f s k ≡ inj₂ b)
  Mono f = ∀ n → ∀ s₁ b₁ → f s₁ n ≡ inj₂ b₁ →
                 ∀ s → ∀ k → k ≤ n → (∃ λ b → f s k ≡ inj₂ b)

  𝓜₁ : Set
  𝓜₁ = Str A → Str (⊤ ⊎ B)

  𝓜 : Set
  𝓜 = Σ[ f ∈ 𝓜₁ ] (Mono f)

  d : 𝓜 → M 𝓜
  d (f , m) = F (f (a₀ ω) 0) refl
    where
      F : (u : ⊤ ⊎ B) → (f (a₀ ω) 0) ≡ u → M 𝓜
      F (inj₁ tt) _ = inj₁ tt
      F (inj₂ b) p = inj₂ (λ a →
        let (b' , p') = m 0 (a₀ ω) b p (a ω) 0 z≤n
            f' = λ s n → f (a ∷ s) (suc n)
            m' : Mono f'
            m' = λ {n s₁ b₁ p₁ s k k≤n →
                      m (suc n) (a ∷ s₁) b₁ p₁ (a ∷ s) (suc k) (s≤s k≤n)}
        in b' , f' , m')

  corec₁ : ∀{X} → (c : X → M X) → X → 𝓜₁
  corec₁ c x s n    with c x
  corec₁ c x s n       | inj₁ tt = inj₁ tt
  corec₁ c x s zero    | inj₂ g  = inj₂ (proj₁ (g (hd s)))
  corec₁ c x s (suc n) | inj₂ g  = corec₁ c (proj₂ (g (hd s))) (tl s) n

  corec₂ : ∀{X} → (c : X → M X) (x : X) → Mono (corec₁ c x)
  corec₂ c x n s₁ b₁ p₁ s k k≤n with c x
  corec₂ c x n s₁ b₁ () s k k≤n | inj₁ tt
  corec₂ c x n s₁ b₁ p₁ s zero k≤n | inj₂ g = (proj₁ (g (hd s)) , refl)
  corec₂ c x n s₁ b₁ p₁ s (suc k) sk≤n | inj₂ g = {!!}
    -- corec₂ c
    --        (proj₂ (g (hd s)))
    --        n
    --        (tl s)
    --        (proj₁ (g (hd s)))
    --        {!!}
    --        (tl s) k (pred-≤ sk≤n)

  -- compute' : ∀{X} (c : X → M X) (x : X) →
  --           ∀ a → d (corec c x) a ≡ M₁ (corec c) (c x) a
  -- compute' c x a =
  --   begin
  --     d (corec c x) a
  --   ≡⟨ refl ⟩
  --     ((corec c x) (a ω) 0 , λ s n → (corec c x) (a ∷ s) (suc n))
  --   ≡⟨ refl ⟩
  --     (proj₁ (c x (hd (a ω)))
  --     , λ s n → corec c (proj₂ (c x (hd (a ∷ s)))) (tl (a ∷ s)) n)
  --   ≡⟨ refl ⟩
  --     (proj₁ (c x a) , λ s n → corec c (proj₂ (c x a)) (λ n → s n) n)
  --   ≡⟨ refl ⟩
  --     (proj₁ (c x a) , λ s n → corec c (proj₂ (c x a)) s n)
  --   ≡⟨ refl ⟩
  --     (proj₁ (c x a) , λ s → corec c (proj₂ (c x a)) s)
  --   ≡⟨ refl ⟩
  --     (proj₁ (c x a) , corec c (proj₂ (c x a)))
  --   ≡⟨ refl ⟩
  --     M₁ (corec c) (c x) a
  --   ∎

  -- compute : ∀{X} (c : X → M X) (x : X) →
  --           d (corec c x) ≡ M₁ (corec c) (c x)
  -- compute c x =
  --   begin
  --     d (corec c x)
  --   ≡⟨ refl ⟩
  --     (λ a → d (corec c x) a)
  --   ≡⟨ refl ⟩ -- Same as in compute'
  --     (λ a → M₁ (corec c) (c x) a)
  --   ≡⟨ refl ⟩
  --     M₁ (corec c) (c x)
  --   ∎
