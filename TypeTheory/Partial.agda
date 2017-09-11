mutual
  data ℕμ : Set where
    zero : ℕμ
    succ : ℕμ → ℕμ
    delay : ℕν → ℕμ

  record ℕν : Set where
    coinductive
    field step : ℕμ

open ℕν public

mutual
  data _≤μ_ : ℕμ → ℕμ → Set where
    -- Standard part of the order
    le₀ : (y : ℕμ) → zero ≤μ y
    leₛ : {x y : ℕμ} → x ≤μ y → succ x ≤μ succ y
    -- We can have finite delays on the left and on the right...
    le-stepₗ : {m : ℕν} {y : ℕμ} → step m ≤μ y → delay m ≤μ y
    le-stepᵣ : {x : ℕμ} {n : ℕν} → x ≤μ step n → x ≤μ delay n
    -- or an abritrary sequence of delays on both sides.
    le-step : {m n : ℕν} → m ≤ n → delay m ≤μ delay n

  record _≤_ (m n : ℕν) : Set where
    coinductive
    field step≤ : (step m) ≤μ (step m)

open _≤_ public

≤μ-refl : (x : ℕμ) → x ≤μ x
≤-refl : (m : ℕν) → m ≤ m

step≤ (≤-refl m) = ≤μ-refl (step m)

≤μ-refl zero = le₀ zero
≤μ-refl (succ x) = leₛ (≤μ-refl x)
≤μ-refl (delay x) = le-step (≤-refl x)
