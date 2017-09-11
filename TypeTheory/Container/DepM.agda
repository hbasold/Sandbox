{-# OPTIONS --sized-types --without-K #-}
module DepM where

open import Level using (Level)
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Unit
open import Data.Empty
open import Data.Vec hiding (_∈_; [_])
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Sum
open import Size

Fam : Set → Set₁
Fam I = I → Set

Fam₂ : {I : Set} → (I → Set) → Set₁
Fam₂ {I} J = (i : I) → J i → Set

-- | Morphisms between families
MorFam : {I : Set} (P₁ P₂ : Fam I) → Set
MorFam {I} P₁ P₂ = (x : I) → P₁ x → P₂ x

_⇒_ = MorFam

compMorFam : {I : Set} {P₁ P₂ P₃ : Fam I} →
             MorFam P₁ P₂ → MorFam P₂ P₃ → MorFam P₁ P₃
compMorFam f₁ f₂ a = f₂ a ∘ f₁ a

_⊚_ = compMorFam

-- | Reindexing of families
_* : {I J : Set} → (I → J) → Fam J → Fam I
(u *) P = P ∘ u

-- | Reindexing on morphisms of families
_*₁ : {I J : Set} → (u : I → J) →
      {P₁ P₂ : Fam J} → (P₁ ⇒ P₂) → (u *) P₁ ⇒ (u *) P₂
(u *₁) f i = f (u i)

-- | This notation for Π-types is more useful for our purposes here.
Π : (A : Set) (P : Fam A) → Set
Π A P = (x : A) → P x

-- | Fully general Σ-type, which we need to interpret the interpretation
-- of families of containers as functors for inductive types.
data Σ' {A B : Set} (f : A → B) (P : Fam A) : B → Set where
  ins : (a : A) → P a → Σ' f P (f a)

p₁' : {A B : Set} {u : A → B} {P : Fam A} {b : B} →
      Σ' u P b → A
p₁' (ins a _) = a

p₂' : {A B : Set} {u : A → B} {P : Fam A} {b : B} →
      (x : Σ' u P b) → P (p₁' x)
p₂' (ins _ x) = x

p₌' : {A B : Set} {u : A → B} {P : Fam A} {b : B} →
      (x : Σ' u P b) → u (p₁' x) ≡ b
p₌' (ins _ _) = refl

ins' : {A B : Set} {u : A → B} {P : Fam A} →
       (a : A) → (b : B) → u a ≡ b → P a → Σ' u P b
ins' a ._ refl x = ins a x

Σ'-eq : {A B : Set} {f : A → B} {P : Fam A} →
        (a a' : A) (x : P a) (x' : P a')
        (a≡a' : a ≡ a') (x≡x' : subst P a≡a' x ≡ x') →
        subst (Σ' f P) (cong f a≡a') (ins a x) ≡ ins a' x'
Σ'-eq a .a x .x refl refl = refl

Σ-eq : {a b : Level} {A : Set a} {B : A → Set b} →
       (a a' : A) (x : B a) (x' : B a')
       (a≡a' : a ≡ a') (x≡x' : subst B a≡a' x ≡ x') →
       (a , x) ≡ (a' , x')
Σ-eq a .a x .x refl refl = refl

×-eq : {ℓ : Level} {A : Set ℓ} {B : Set ℓ} →
       (a a' : A) (b b' : B) →
       a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
×-eq a .a b .b refl refl = refl

×-eqˡ : {A B : Set} {a a' : A} {b b' : B} → (a , b) ≡ (a' , b') → a ≡ a'
×-eqˡ refl = refl

×-eqʳ : {A B : Set} {a a' : A} {b b' : B} → (a , b) ≡ (a' , b') → b ≡ b'
×-eqʳ refl = refl

-- | Comprehension
⟪_⟫ : {I : Set} → Fam I → Set
⟪_⟫ {I} B = Σ I B

⟪_⟫² : {I J : Set} → (J → Fam I) → Fam J
⟪_⟫² {I} B j = Σ I (B j)

π : {I : Set} → (B : Fam I) → ⟪ B ⟫ → I
π B = proj₁

_⊢₁_ : {I : Set} {A : Fam I} → (i : I) → A i → ⟪ A ⟫
i ⊢₁ a = (i , a)

_,_⊢₂_ : {I : Set} {A : Fam I} {B : Fam ⟪ A ⟫} →
         (i : I) → (a : A i) → B (i , a) → ⟪ B ⟫
i , a ⊢₂ b = ((i , a) , b)

-- Not directly definable...
-- record Π' {A B : Set} (u : A → B) (P : A → Set) : B → Set where
--  field
--    app : (a : A) → Π' u P (u a) → P a

-- | ... but this does the job.
Π' : {I J : Set} (u : I → J) (P : Fam I) → Fam J
Π' {I} u P j = Π (∃ λ i → u i ≡ j) (λ { (i , _) → P i})

Π'' : {I J : Set} (u : I → J) (j : J) (P : Fam (∃ λ i → u i ≡ j)) → Set
Π'' {I} u j P = Π (∃ λ i → u i ≡ j) P

-- | Application for fully general Π-types.
app : {I J : Set} {u : I → J} {P : Fam I} →
      (u *) (Π' u P) ⇒ P
app i f = f (i , refl)

-- | Abstraction for fully general Π-types.
abs : {I J : Set} {u : I → J} {P : Fam I} →
      ((i : I) → P i) → ((j : J) → Π' u P j)
abs {u = u} f .(u i) (i , refl) = f i

-- | Abstraction for fully general Π-types.
abs' : {I J : Set} {u : I → J} {P : Fam I} {X : Fam J} →
      ((u *) X ⇒ P) → (X ⇒ Π' u P)
abs' {u = u} f .(u i) x (i , refl) = f i x

-- | Abstraction for fully general Π-types.
abs'' : {I J : Set} {u : I → J} {P : Fam I} →
        (j : J) → ((i : I) → u i ≡ j → P i) → Π' u P j
abs'' j f (i , p) = f i p

abs₃ : {I J : Set} {u : I → J} (j : J) {P : Fam (Σ I (λ i → u i ≡ j))} →
       ((i : I) → (p : u i ≡ j) → P (i , p)) → Π'' u j P
abs₃ j f (i , p) = f i p

-- | Functorial action of Π'
Π'₁ : {I J : Set} {u : I → J} {P Q : Fam I} →
        (f : P ⇒ Q) → (Π' u P ⇒ Π' u Q)
Π'₁ {u = u} f .(u i) g (i , refl) = f i (app i g)


-- | Dependent polynomials
record DPoly
  {I : Set} -- ^ Outer index
  {J : Set} -- ^ Inner index
  : Set₁ where
  constructor dpoly
  field
    -- J ←t- E -p→ A -s→ I
    A : Set  -- ^ Labels
    s : A → I
    E : Set
    p : E → A
    t : E → J

-- | Interpretation of polynomial as functor
⟦_⟧ : {I : Set} {J : Set} →
    DPoly {I} {J} →
    (X : Fam J) →  -- ^ Parameter
    (Fam I)
⟦_⟧ {I} {N} (dpoly A s E p t) X =
  Σ' s (λ a →
  Π' p (λ e →
    X (t e)
  ) a )

-- | Functorial action of T
⟦_⟧₁ : {I : Set} {J : Set} →
     (P : DPoly {I} {J}) →
     {X Y : J → Set} →
     (f : (j : J) → X j → Y j)
     (i : I) → ⟦ P ⟧ X i → ⟦ P ⟧ Y i
⟦_⟧₁ {I} {J} (dpoly A s E p t) {X} {Y} f .(s a) (ins a v) =
  ins a (Π'₁ ((t *₁) f) a v)

-- | Final coalgebras for dependent polynomials
record M {a : Size} {I} (P : DPoly {I} {I}) (i : I) : Set where
  coinductive
  field
    ξ : ∀ {b : Size< a} → ⟦ P ⟧ (M {b} P) i
open M

ξ'  : ∀ {I P} → {i : I} → M P i → ⟦ P ⟧ (M P) i
ξ' x = ξ x

Rel₂ : {I : Set} → (X Y : I → Set) → Set₁
Rel₂ {I} X Y = (i : I) → X i → Y i → Set

-- | Lifting to relations
⟦_⟧'' : ∀ {I} (P : DPoly {I} {I}) {X Y} → Rel₂ X Y → Rel₂ (⟦ P ⟧ X) (⟦ P ⟧ Y)
⟦ dpoly A s E p t ⟧'' {X} {Y} R i x y =
  ∃ λ a → ∃ λ α → ∃ λ β → Σ[ q ∈ (i ≡ s a) ]
    (subst (⟦ dpoly A s E p t ⟧ X) q x ≡ ins a α
    × (subst (⟦ dpoly A s E p t ⟧ Y) q y) ≡ ins a β
    × ∀ u → R (t (proj₁ u)) (α u) (β u))

[_]_≡₂_ : ∀{I} {X : I → Set} → Rel₂ X X
[ i ] x ≡₂ y = x ≡ y

eq-preserving : ∀ {I P X} (i : I) (x y : ⟦ P ⟧ X i) →
                x ≡ y → ⟦ P ⟧'' (λ i → _≡_) i x y
eq-preserving i x y x≡y = {!!}

mutual
  -- | Equality for M types is given by bisimilarity
  record Bisim {I} {P : DPoly {I} {I}} (i : I) (x y : M P i) : Set where
    coinductive
    field
      ~pr : ⟦ P ⟧'' Bisim i (ξ' x) (ξ' y)
open Bisim public
