module Shallow where

open import Level using (_⊔_) renaming (suc to lsuc)
open import Function
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Nat hiding (_⊔_)
open import Data.Fin
open import Relation.Binary.PropositionalEquality as PE hiding ([_]; subst)

Π : ∀ {a b} (A : Set a) (B : A → Set b) → Set (a ⊔ b)
Π A B = (a : A) → B a

Fam : ∀ {a} → Set a → Set (lsuc a)
Fam {a} I = I → Set a

data Σ' {A B : Set} (f : A → B) (P : Fam A) : B → Set where
  ins : (a : A) → P a → Σ' f P (f a)

Π' : {I J : Set} (u : I → J) (P : Fam I) → Fam J
Π' {I} u P j = Π (∃ λ i → u i ≡ j) (λ { (i , _) → P i})

_* : {I J : Set} → (I → J) → Fam J → Fam I
(u *) A i = A (u i)

Fin⁺ : ℕ → Set
Fin⁺ = Fin ∘ suc

Vec⁺ : ∀ {a} → Set a → ℕ → Set a
Vec⁺ A n = Fin⁺ n → A

[_] : ∀ {a} {A : Set a} → A → Vec⁺ A 0
[ x ] _ = x

_∷_ : ∀ {a} {A : Set a} {n : ℕ} → A → Vec⁺ A n → Vec⁺ A (suc n)
(x ∷ v) zero    = x
(x ∷ v) (suc k) = v k

module Simple where
  module _ where
    mutual
      data U : Set where
        zero : U
        one : U
        sigma : (A : U) → (Elem A → U) → U
        pi : (A : U) → (Elem A → U) → U

      Elem : U → Set
      Elem zero        = ⊥
      Elem one         = ⊤
      Elem (sigma A B) = Σ (Elem A) (λ x → Elem (B x))
      Elem (pi A B)    = Π (Elem A) (λ x → Elem (B x))

module Recursive where
  module _ where
    ∐ : {n : ℕ} {I : Set} → (Fin⁺ n → Fam I) → Fam I
    ∐ {zero}  f   = f zero
    ∐ {suc n} f i = f zero i ⊎ ∐ (λ k → f (suc k)) i

    ∏ : {n : ℕ} {I : Set} → (Fin⁺ n → Fam I) → Fam I
    ∏ {zero}  f   = f zero
    ∏ {suc n} f i = f zero i × ∏ (λ k → f (suc k)) i

    data FP : Set where
      μ : FP
      ν : FP

    mutual
      data U : Set where
        fp : {n : ℕ} (A : U) (o : Vec⁺ U n) →
             FP → Functor [ A ] o → Subst o A → U

      -- | Substitutions
      Subst : {n : ℕ} → Vec⁺ U n → U → Set
      Subst {n} o A = (k : Fin⁺ n) → Elem (o k) → Elem A

      data Functor : {m n : ℕ} → Vec⁺ U m → Vec⁺ U n → Set where
        K : {m : ℕ} (v : Vec⁺ U m) (A : U)     → Functor v [ A ]
        π : {m : ℕ} (v : Vec⁺ U m) (i : Fin⁺ m) → Functor v [ v i ]
        fpF : {m n : ℕ} {v : Vec⁺ U m} {o : Vec⁺ U n} {A : U} →
              FP → Functor (A ∷ v) o → Subst o A → Functor v [ A ]

      Elem : U → Set
      Elem (fp A o μ F u) = {!!} -- LFP F u {!!}
        where
          G : Fam (Elem A) → Fam (Elem A)
          G = IndFun F u

      Elem (fp A o ν F u) = {!!}

      IdxFam : {m : ℕ} → Vec⁺ U m → Set₁
      IdxFam {m} v = (k : Fin⁺ m) → Fam (Elem (v k))

      ⟦_⟧ : {m n : ℕ} {i : Vec⁺ U m} {o : Vec⁺ U n} →
            Functor i o → (IdxFam i → IdxFam o)
      ⟦ K v A ⟧ x k        i = Elem A
      ⟦ π v k ⟧ x zero     i = x k i
      ⟦ π v k ⟧ x (suc ()) i
      ⟦ fpF μ F u ⟧ x = {!!}
      ⟦ fpF ν F u ⟧ x = {!!}

      IndFun : {n : ℕ} {A : U} {o : Vec⁺ U n} →
               (F : Functor [ A ] o) →
               -- (F : Fam (Elem A) → IdxFam o) →
               (u : Subst o A) →
               (Fam (Elem A) → Fam (Elem A))
      IndFun {n} {A} F u X = ∐ f
        where
          f : Fin⁺ n → Fam (Elem A)
          f k = Σ' (u k) (⟦ F ⟧ (λ _ → X) k)

      CoindFun : {n : ℕ} {A : U} {o : Vec⁺ U n} →
                 (F : Functor [ A ] o) →
                 -- (F : Fam (Elem A) → IdxFam o) →
                 (u : Subst o A) →
                 (Fam (Elem A) → Fam (Elem A))
      CoindFun {n} {A} F u X = ∏ f
        where
          f : Fin⁺ n → Fam (Elem A)
          f k = Π' (u k) (⟦ F ⟧ (λ _ → X) k)

      data LFP {n : ℕ} {A : U} {o : Vec⁺ U n}
               (F : Functor [ A ] o) (u : Subst o A) : Elem A → Set where
--        α : (a : Elem A) → IndFun F u (LFP F u) a → LFP F u a

{-
      data U : Set where
        fp : {n : ℕ} (C : Cat) (o : Vec Cat n) →
             FP → Functor [ C ] o → Subst o C → U

      -- | Index of a fibre
      Cat : Set
      Cat = Σ U Elem

      Mor : Cat → Set
      Mor C = ? -- (A , x) = -- Σ U (λ B → {!Elem B → x!})

      -- | Substitutions
      Subst : {n : ℕ} → Vec Cat n → Cat → Set
      Subst {n} o C = Vec {!!} n

      data Functor : {m n : ℕ} → Vec Cat m → Vec Cat n → Set where
        K : {m : ℕ} (v : Vec Cat m) → {A : U} → (x : Elem A) → Functor v [ , x ]
        π : {m : ℕ} (v : Vec Cat m) → (i : Fin m) → Functor v [ lookup i v ]
        fpF : {m n : ℕ} {v : Vec Cat m} {o : Vec Cat n} {C : Cat} →
              FP → Functor (C ∷ v) o → Subst o C → Functor v [ C ]

      Elem : U → Set
      Elem x = {!!}
-}

module DepPoly where
  module _ where
    record DPoly (J I : Set) : Set₁ where
      constructor dpoly
      field
        -- J <- Shapes -> Pos -> I
        Pos : Set
        Shapes : Set
        s : Shapes → J
        f : Shapes → Pos
        t : Pos → I
    open DPoly

    ⟦_⟧ : {J I : Set} → DPoly J I → Fam J → Fam I
    ⟦ dpoly A B s f t ⟧ X = Σ' t (Π' f ((s *) X))

    data W {I : Set} (P : DPoly I I) : I → Set where
      α : (i : I) → ⟦ P ⟧ (W P) i → W P i

    record M {I : Set} (P : DPoly I I) (i : I) : Set where
      coinductive
      field
        ξ : ⟦ P ⟧ (M P) i

    data FP : Set where
      μ : FP
      ν : FP

    mutual
      data U : Set where
        fp : {n : ℕ} (A : U) (o : Vec⁺ U n) →
             FP → Functor [ A ] o → Subst o A → U

      -- | Substitutions
      Subst : {n : ℕ} → Vec⁺ U n → U → Set
      Subst {n} o A = (k : Fin⁺ n) → Elem (o k) → Elem A

      data Functor : {m n : ℕ} → Vec⁺ U m → Vec⁺ U n → Set where
        K : {m : ℕ} (v : Vec⁺ U m) {I A : U} → (Elem A → Elem I) → Functor v [ I ]
        π : {m : ℕ} (v : Vec⁺ U m) (i : Fin⁺ m) → Functor v [ v i ]
        fpF : {m n : ℕ} {v : Vec⁺ U m} {o : Vec⁺ U n} {A : U} →
              FP → Functor (A ∷ v) o → Subst o A → Functor v [ A ]

      Elem : U → Set
      Elem (fp A o μ F u) = Σ (Elem A) (W (Poly F u))
      Elem (fp A o ν F u) = {!!}

      Poly : {n : ℕ} {I : U} {o : Vec⁺ U n} (F : Functor [ I ] o) →
             (u : Subst o I) → DPoly (Elem I) (Elem I)
      Poly         (K ._ {J} {A} B) u =
        dpoly (Elem A) ⊥ (λ ()) (λ ()) (u zero ∘ B)
      Poly {I = I} (π ._ i)         u =
        dpoly (Elem I) (Elem I) id id id
      Poly         (fpF μ F v) u =
        {!!}
      Poly         (fpF ν F v) u =
        {!!}
