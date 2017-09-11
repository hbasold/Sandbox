open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
open ≡-Reasoning
open import Data.Empty
open import Data.Unit
open import Data.Sum as Sum
open import Data.Product as Prod

record ℕ∞ : Set where
  coinductive
  field pred : ⊤ ⊎ ℕ∞

open ℕ∞ public

data-~ℕ∞~ : ⊤ ⊎ ℕ∞ → ⊤ ⊎ ℕ∞ → Set

record _~ℕ∞~_ (n m : ℕ∞) : Set where
  coinductive
  field
    pred~ : data-~ℕ∞~ (pred n) (pred m)
open _~ℕ∞~_ public

data-~ℕ∞~ (inj₁ tt) (inj₁ tt) = ⊤
data-~ℕ∞~ (inj₁ tt) (inj₂ m') = ⊥
data-~ℕ∞~ (inj₂ n') (inj₁ tt) = ⊥
data-~ℕ∞~ (inj₂ n') (inj₂ m') = n' ~ℕ∞~ m'

refl-ℕ∞ : {n : ℕ∞} → n ~ℕ∞~ n
pred~ (refl-ℕ∞ {n}) with pred n
pred~ refl-ℕ∞ | inj₁ tt = tt
pred~ refl-ℕ∞ | inj₂ n' = refl-ℕ∞

∞ : ℕ∞
pred ∞ = inj₂ ∞

succ : ℕ∞ → ℕ∞
pred (succ n) = inj₂ n

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
pred (n +∞ m) with pred n | pred m
pred (n +∞ m) | inj₁ tt | inj₁ tt = inj₁ tt
pred (n +∞ m) | inj₁ tt | inj₂ m' = inj₂ m'
pred (n +∞ m) | inj₂ n' | inj₁ tt = inj₂ n'
pred (n +∞ m) | inj₂ n' | inj₂ m' = inj₂ (record { pred = inj₂ (n' +∞ m') })

+∞-comm : (n m : ℕ∞) → (n +∞ m) ~ℕ∞~ (m +∞ n)
pred~ (+∞-comm n m) with pred n | pred m
pred~ (+∞-comm n m) | inj₁ tt | inj₁ tt = tt
pred~ (+∞-comm n m) | inj₁ tt | inj₂ m' = refl-ℕ∞
pred~ (+∞-comm n m) | inj₂ n' | inj₁ tt = refl-ℕ∞
pred~ (+∞-comm n m) | inj₂ n' | inj₂ m'
  = record { pred~ = +∞-comm n' m' }

2×_ : ℕ∞ → ℕ∞
pred (2× n) with pred n
pred (2× n) | inj₁ tt = inj₁ tt
pred (2× n) | inj₂ n' = inj₂ (record { pred = inj₂ (2× n') })

StrData : Set → (ℕ∞ → Set) → ⊤ ⊎ ℕ∞ → Set
StrData A F (inj₁ tt) = ⊤
StrData A F (inj₂ d') = A × F d'

record Str (A : Set) (d : ℕ∞) : Set where
  coinductive
  field
    str-out : StrData A (Str A) (pred d)
open Str public

reidx-Str : ∀{n m A} → n ~ℕ∞~ m → Str A n → Str A m
str-out (reidx-Str {n} {m} p s) with pred n | pred m | pred~ p | str-out s
str-out (reidx-Str p s) | inj₁ tt | inj₁ tt | _  | _ = tt
str-out (reidx-Str p s) | inj₁ tt | inj₂ m' | () | _
str-out (reidx-Str p s) | inj₂ n' | inj₁ tt | () | _
str-out (reidx-Str p s) | inj₂ n' | inj₂ m' | q  | (a , s')
  = (a , reidx-Str q s')

tl : ∀{d A} → Str A (succ d) → Str A d
tl {d} s = proj₂ (str-out s)

tl₂ : ∀{d A} → Str A (succ (succ d)) → Str A d
tl₂ {d} s = proj₂ (str-out (proj₂ (str-out s)))

even : ∀{d A} → Str A (2× d) → Str A d
str-out (even {d} s) with pred d | str-out s
str-out (even s) | inj₁ tt | tt = tt
str-out (even s) | inj₂ d' | (a , s') with str-out s'
str-out (even s) | inj₂ d' | (a , s') | (_ , s'') = (a , even s'')

zip₂ : ∀{m n A} → Str A m → Str A n → Str A (m +∞ n)
str-out (zip₂ {m} {n} s t) with pred m | pred n | str-out s | str-out t
str-out (zip₂ s t) | inj₁ tt | inj₁ tt | tt       | _ = tt
str-out (zip₂ s t) | inj₁ tt | inj₂ n' | tt       | u = u
str-out (zip₂ s t) | inj₂ m' | inj₁ tt | (a , s') | tt = (a , s')
str-out (zip₂ s t) | inj₂ m' | inj₂ n' | (a , s') | (b , t')
  = (a , record { str-out = (b , zip₂ s' t') })

𝔹 : Set
𝔹 = ⊤ ⊎ ⊤

l r : 𝔹
l = inj₁ tt
r = inj₂ tt

L R : Str 𝔹 ∞
str-out L = (l , L)
str-out R = (r , R)

restr : ∀{A} → Str A ∞ → (d : ℕ∞) → Str A d
str-out (restr s d) with pred d | str-out s
str-out (restr s d) | inj₁ tt | _ = tt
str-out (restr s d) | inj₂ d' | (a , s') = (a , restr s' d')

foo : ∀{d} → Str 𝔹 d
str-out (foo {d}) with pred d
str-out foo | inj₁ tt = tt
str-out foo | inj₂ d' = (l , even {!!})
