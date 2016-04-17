module Relations where

open import Level as Level using (zero)
open import Size
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
open ≡-Reasoning

RelTrans : Set → Set₁
RelTrans B = Rel B Level.zero → Rel B Level.zero

Monotone : ∀{B} → RelTrans B → Set₁
Monotone F = ∀ {R S} → R ⇒ S → F R ⇒ F S

-- | Useful example of a compatible up-to technique: equivalence closure.
data EquivCls {B : Set} (R : Rel B Level.zero) : Rel B Level.zero where
  cls-incl : {a b : B} → R a b → EquivCls R a b
  cls-refl : {b : B} → EquivCls R b b
  cls-sym  : {a b : B} → EquivCls R a b → EquivCls R b a
  cls-trans : {a b c : B} → EquivCls R a b → EquivCls R b c → EquivCls R a c

-- | The operation of taking the equivalence closure is monotone.
equivCls-monotone : ∀{B} → Monotone {B} EquivCls
equivCls-monotone R≤S (cls-incl xRy)  = cls-incl (R≤S xRy)
equivCls-monotone R≤S cls-refl        = cls-refl
equivCls-monotone R≤S (cls-sym p)     = cls-sym (equivCls-monotone R≤S p)
equivCls-monotone R≤S (cls-trans p q) =
  cls-trans (equivCls-monotone R≤S p) (equivCls-monotone R≤S q)

-- | The equivalence closure is indeed a closure operator.
equivCls-expanding : ∀{B R} → R ⇒ EquivCls {B} R
equivCls-expanding p = cls-incl p

equivCls-idempotent : ∀{B R} → EquivCls (EquivCls R) ⇒ EquivCls {B} R
equivCls-idempotent (cls-incl p)    = p
equivCls-idempotent cls-refl        = cls-refl
equivCls-idempotent (cls-sym p)     = cls-sym (equivCls-idempotent p)
equivCls-idempotent (cls-trans p q) =
  cls-trans (equivCls-idempotent p) (equivCls-idempotent q)

-- | Equivalence closure gives indeed equivalence relation
equivCls-equiv : ∀{A} → (R : Rel A _) → IsEquivalence (EquivCls R)
equivCls-equiv R = record
  { refl  = cls-refl
  ; sym   = cls-sym
  ; trans = cls-trans
  }
