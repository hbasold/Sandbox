{-# OPTIONS --copatterns --sized-types --without-K #-}
module PolyFinalCoalg where

open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Unit as Unit
open import Data.Empty
open import Data.Vec hiding (_∈_; [_])
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Sum as Sum
open import Size

open import Poly

-- | Indexed product
_×ᵢ_ : {I : Set} → Fam I → Fam I → Fam I
(A ×ᵢ B) i = A i × B i

-- | Product of indexed functors
_×ᵢ'_ : {I J K : Set} →
        (Fam K → Fam I) → (Fam J → Fam I) → (Fam K × Fam J → Fam I)
(F ×ᵢ' G) (X , Y) = F X ×ᵢ G Y

record Isomorphic (A B : Set) : Set where
--  constructor isIso
  field
    f : A → B
    f⃖ : B → A
    is-invˡ : (a : A) → f⃖ (f a) ≡ a
    is-invʳ : (b : B) → f (f⃖ b) ≡ b

_≃_ = Isomorphic

_≃'_ : {I : Set} → Fam I → Fam I → Set
_≃'_ {I} A B = (i : I) → A i ≃ B i

-- | Avoid setoids for now
postulate
  Π'-ext : {I J : Set} {u : I → J} {P : Fam I} →
           (j : J) (f g : Π' u P j) →
           ((i : I) → (p : u i ≡ j) → f (i , p) ≡ g (i , p)) → f ≡ g
  Π'-ext' : {I J : Set} {u : I → J} {P : Fam I} →
           (f g : (i : I) → Π' u P (u i)) →
           ((i : I) → app i (f i) ≡ app i (g i)) → (i : I) → f i ≡ g i

-- | Dependent polynomials
record ParamPoly {I J : Set}  : Set₁ where
  constructor ppoly
  field
    -- J ←t- B -p→ A -s→ I
    A : Set  -- ^ Labels
    s : A → I
    B : Set
    p₁ p₂ : B → A
    t₁ : B → J
    t₂ : B → I

first : {I J : Set} → ParamPoly {I} {J} → DPoly {I} {J}
first (ppoly A s B p₁ p₂ t₁ t₂) = dpoly A s B p₁ t₁

second : {I J : Set} → ParamPoly {I} {J} → DPoly {I} {I}
second (ppoly A s B p₁ p₂ t₁ t₂) = dpoly A s B p₂ t₂


R : {I J : Set} → ParamPoly {I} {J} →
    (X : Fam J) → (Y : Fam I) → Fam I
R (ppoly A s B p₁ p₂ t₁ t₂) X Y =
  Σ' s (Π' p₁ ((t₁ *) X) ×ᵢ Π' p₂ ((t₂ *) Y))

data ⊤' (I : Set) : I → Set where
  tt : (i : I) → ⊤' I i

⊤'-unique : {I : Set} {i : I} → (x y : ⊤' I i) → x ≡ y
⊤'-unique (tt i) (tt .i) = refl

triv-param : {I J : Set} → (P : ParamPoly {I} {J}) →
             (Y : Fam I) → R P (⊤' J) Y ≃' T (second P) Y
triv-param {I} {J} (ppoly A s B p₁ p₂ t₁ t₂) Y i =
  record
  { f = f i
  ; f⃖ = g i
  ; is-invˡ = is-invˡ i
  ; is-invʳ = is-invʳ i
  }
  where
    P = ppoly A s B p₁ p₂ t₁ t₂

    f : (i : I) → R P (⊤' J) Y i → T (second P) Y i
    f ._ (ins a (v₁ , v₂)) = ins a v₂

    triv : (a : A) → Π' p₁ ((t₁ *) (⊤' J)) a
    triv a = abs (λ b → tt (t₁ b)) a

    g : (i : I) → T (second P) Y i → R P (⊤' J) Y i
    g ._ (ins a v) = ins a (triv a , v)

    is-invˡ : (i : I) → (x : R P (⊤' J) Y i) → g i (f i x) ≡ x
    is-invˡ ._ (ins a (v₁ , v₂)) =
      Σ'-eq a a (triv a , v₂) (v₁ , v₂)
      refl
      (×-eq (triv a) v₁ v₂ v₂
        (Π'-ext a (triv a) v₁ (lem a v₁))
        refl)
      where
        lem : (a : A) (v₁ :  Π' p₁ ((t₁ *) (⊤' J)) a)
              (i₁ : B) (p : p₁ i₁ ≡ a) →
              triv a (i₁ , p) ≡ v₁ (i₁ , p)
        lem ._ v₁ i₁ refl = ⊤'-unique (tt (t₁ i₁)) (app i₁ v₁)

    is-invʳ : (i : I) → (x : T (second P) Y i) → f i (g i x) ≡ x
    is-invʳ ._ (ins a x) = refl

triv : {I J : Set} (P : DPoly {I} {J}) → T P (⊤' J) ≃' toFam (DPoly.s P)
triv {I} {J} (dpoly A s E p t) i =
  record
  { f = f i
  ; f⃖ = g i
  ; is-invˡ = p₁ i
  ; is-invʳ = p₂ i
  }
  where
    P = dpoly A s E p t

    f : (i : I) → T P (⊤' J) i → toFam s i
    f ._ (ins a v) = (a , refl)

    g : (i : I) → toFam s i → T P (⊤' J) i
    g ._ (a , refl) = ins a (abs'' a v)
      where
        v : (b : E) → p b ≡ a → ⊤' J (t b)
        v b _ = tt (t b)

    p₁ : (i : I) → (x : T (dpoly A s E p t) (⊤' J) i) → g i (f i x) ≡ x
    p₁ ._ (ins a v) =
      Σ'-eq a a (abs'' a (λ b _ → tt (t b))) v
            refl
            (Π'-ext a (abs'' a (λ b _ → tt (t b))) v
                    (λ b p₂ → ⊤'-unique (tt (t b)) (v (b , p₂))))

    p₂ : (i : I) (b : toFam s i) → f i (g i b) ≡ b
    p₂ ._ (a , refl) = refl

foo : {A C P : Set} (B : Fam A) (D : Fam C) (Q : Fam P) (X : Set) →
      Σ (A × C) (λ {(a , c) → (B a → X) × (D c → Σ P (λ p → Q p → X)) })
      ≃
      Σ (A × Σ C (λ c → D c → P))
        (λ {(a , c , t) → ((B a → X) × ((Σ (D c) ((t *) Q)) → X))})
foo {A} {C} {P} B D Q X =
  record
  { f = f
  ; f⃖ = g
  ; is-invˡ = {!!}
  ; is-invʳ = {!!}
  }
  where
    f : Σ (A × C) (λ {(a , c) → (B a → X) × (D c → Σ P (λ p → Q p → X)) }) →
        Σ (A × Σ C (λ c → D c → P))
          (λ {(a , c , t) → ((B a → X) × ((Σ (D c) ((t *) Q)) → X))})
    f ((a , c) , t) =
      ((a , c , (λ d → proj₁ (proj₂ t d) ))
      , ((proj₁ t) , (λ { (d , q) → proj₂ (proj₂ t d) q})))

    g : Σ (A × Σ C (λ c → D c → P))
          (λ {(a , c , t) → ((B a → X) × ((Σ (D c) ((t *) Q)) → X))}) →
        Σ (A × C) (λ {(a , c) → (B a → X) × (D c → Σ P (λ p → Q p → X)) })
    g ((a , c , t₁) , t₂) =
      ((a , c)
      , (proj₁ t₂)
      , (λ d → (t₁ d , (λ q → proj₂ t₂ (d , q)))))

δ : {I : Set} → I → I × I
δ i = (i , i)

bar : {I K L : Set} (t : K → I) (v : L → I) (A : Fam K) (B : Fam L) →
      (Σ' t A ×ᵢ Σ' v B) ≃' (δ *) (Σ' (t ⊗ v) ((proj₁ *) A ×ᵢ (proj₂ *) B))
bar {I} {K} {L} t v A B i =
  record
  { f = f i
  ; f⃖ = g i
  ; is-invˡ = {!!}
  ; is-invʳ = {!!}
  }
  where
    f : (i : I) →
        (Σ' t A ×ᵢ Σ' v B) i → (Σ' (t ⊗ v) ((proj₁ *) A ×ᵢ (proj₂ *) B)) (i , i)
    f .(t k) (ins k x , y) = h k x (t k) refl y
      where
        h : (k : K) (x : A k) (i : I) (p : t k ≡ i) →
            (Σ' v B) i → (Σ' (t ⊗ v) ((proj₁ *) A ×ᵢ (proj₂ *) B)) (i , i)
        h k x ._ p (ins l y) =
          ins' (k , l)
               ((v l) , (v l))
               (⊗-eq {f = t} {v} k l p)
               (x , y)

    g : (i : I) →
        (Σ' (t ⊗ v) ((proj₁ *) A ×ᵢ (proj₂ *) B)) (i , i) → (Σ' t A ×ᵢ Σ' v B) i
    g i x =
      let
        k = proj₁ (p₁' x)
        l = proj₂ (p₁' x)

        q₁ : t k ≡ i
        q₁ = ×-eqˡ (p₌' x)

        q₂ : v l ≡ i
        q₂ = ×-eqʳ (p₌' x)

        u : A k × B l
        u = p₂' x
      in (ins' k i q₁ (proj₁ u) , ins' l i q₂ (proj₂ u))

_∣_ : {I J : Set} → Fam I → Fam J → Fam (I ⊎ J)
X ∣ Y = [ X , Y ]′

PB : {A₁ A₂ I : Set} → (A₁ → I) → (A₂ → I) → Set
PB {A₁} {A₂} f g = Σ[ x ∈ A₁ × A₂ ] (f (proj₁ x) ≡ g (proj₂ x))

PB-idx : {A₁ A₂ I : Set} → (f : A₁ → I) → (g : A₂ → I) → (PB f g → I)
PB-idx f _ ((x₁ , x₂) , _) = f x₁

_⊎'_ : {I J K : Set} → DPoly {I} {J} → DPoly {I} {K} → DPoly {I} {J ⊎ K}
(dpoly A₁ s₁ B₁ p₁ t₁) ⊎' (dpoly A₂ s₂ B₂ p₂ t₂)
  = dpoly A (PB-idx s₁ s₂) (U₁ ⊎ U₂) [ q₁ , q₂ ]′ (Sum.map (t₁ ∘ r₁) (t₂ ∘ r₂))
  where
    A = PB s₁ s₂
    U₁ = PB {A} (proj₁ ∘ proj₁) p₁
    U₂ = PB {A} (proj₂ ∘ proj₁) p₂
    q₁ : U₁ → A
    q₁ = proj₁ ∘ proj₁
    q₂ : U₂ → A
    q₂ = proj₁ ∘ proj₁
    r₁ : U₁ → B₁
    r₁ = proj₂ ∘ proj₁
    r₂ : U₂ → B₂
    r₂ = proj₂ ∘ proj₁

parametric-poly-by-sum : {I J K : Set} →
  (P : DPoly {I} {J}) → (Q : DPoly {I} {K}) →
  ∀ X Y → (T P ×ᵢ' T Q)(X , Y) ≃' T (P ⊎' Q) (X ∣ Y)
parametric-poly-by-sum {I} {J} P Q X Y i =
  record
  { f = f i
  ; f⃖ = g i
  ; is-invˡ = {!!}
  ; is-invʳ = {!!}
  }

  where

  f : (i : I) → (T P ×ᵢ' T Q) (X , Y) i → T (P ⊎' Q) (X ∣ Y) i
  f ._ (ins a v , y) = h a v (DPoly.s P a) refl y
    where
      h : (a : DPoly.A P)
          (v : Π' (DPoly.p P) (λ e → X (DPoly.t P e)) a)
          (i : I)
          (p : DPoly.s P a ≡ i) →
          T Q Y i → T (P ⊎' Q) (X ∣ Y) i
      h a₁ v₁ ._ p (ins a₂ v₂) = ins' a₃ (DPoly.s Q a₂) p₃ v₃
        where
          a₃ : DPoly.A (P ⊎' Q)
          a₃ = (a₁ , a₂) , p

          p₃ : DPoly.s (P ⊎' Q) a₃ ≡ DPoly.s Q a₂
          p₃ = trans refl p

          v₃ : Π' (DPoly.p (P ⊎' Q)) (λ e → (X ∣ Y) (DPoly.t (P ⊎' Q) e)) a₃
          v₃ = abs'' a₃ (v' a₃ refl)
            where
            v' : (u : DPoly.A (P ⊎' Q)) →
                 (a₁ , a₂) ≡ proj₁ u →
                 (i₁ : DPoly.E (P ⊎' Q)) →
                 DPoly.p (P ⊎' Q) i₁ ≡ u →
                 ((X ∣ Y) (DPoly.t (P ⊎' Q) i₁))
            v' u r (inj₁ ((.u , b) , q)) refl = v₁ (b , sym (trans (×-eqˡ r) q))
            v' u r (inj₂ ((.u , b) , q)) refl = v₂ (b , sym (trans (×-eqʳ r) q))

  g :  (i : I) → T (P ⊎' Q) (X ∣ Y) i → (T P ×ᵢ' T Q) (X , Y) i
  g ._ (ins x v) =
    (ins (proj₁ (proj₁ x)) v₁
    , ins' a₂ (DPoly.s P a₁) (sym (proj₂ x)) v₂)
    where
      a₁ = proj₁ (proj₁ x)
      a₂ = proj₂ (proj₁ x)

      v₁ : Π' (DPoly.p P) (((DPoly.t P) *) X) a₁
      v₁ = abs'' a₁ (v₁' a₁ refl)
        where
          v₁' : (a : DPoly.A P) (p : a₁ ≡ a) (b : DPoly.E P) →
                DPoly.p P b ≡ a → X (DPoly.t P b)
          v₁' ._ p b refl = v ((inj₁ ((x , b) , p)) , refl)

      v₂ : Π' (DPoly.p Q) (((DPoly.t Q) *) Y) a₂
      v₂ = abs'' a₂ (v₂' a₂ refl)
        where
          v₂' : (a : DPoly.A Q) (p : a₂ ≡ a) (b : DPoly.E Q) →
                DPoly.p Q b ≡ a → Y (DPoly.t Q b)
          v₂' ._ p b refl = v ((inj₂ ((x , b) , p)) , refl)


{-
 : {I J : Set} → (P : DPoly {I} {J}) → (Q : DPoly {I} {J}) →
       let H = λ X Y → ⟦ P ⟧ X ×ᵢ ⟦ Q ⟧
       in 
-}
