module TestsTransport where

open import Function
open import Data.Product
open import Relation.Binary.PropositionalEquality as P
open ≡-Reasoning

open import Isomorphisms
open import Tests

Foo : (A : Set) → (T : Testable A) →
      (x y : A) → (φ : Test T) → Set
Foo A T x y ⊤ =
  _⊨_ {A} {T} x ⊤ ≡ _⊨_ {A} {T} y ⊤
Foo A T x y ⊥ =
  _⊨_ {A} {T} x ⊥ ≡ _⊨_ {A} {T} y ⊥
Foo A T x y (nonTriv nt) = sat≡ (kind T) (subT nt) (obs T)
  where
    sat≡ : (k : Kind) → SubTests T k → (A → ObsTy (index T) (parts T) k) → Set
    sat≡ ind φs o =
      cotuple (λ i y → y ⊨ app φs i) (o x)
      ≡ cotuple (λ i y → y ⊨ app φs i) (o y)
    sat≡ coind (i , φ) o =
      app (o x) i ⊨ φ ≡ app (o y) i ⊨ φ

-- Note: Maybe Reveal_is_ can help to match on (kind T)??

{-
≃-transport : {A B : Set} → {T : Testable A} → (I : Iso A B) →
              (x y : A) → x ≃〈 T 〉 y →
              (Iso.iso I x) ≃〈 iso-testable T I 〉 (Iso.iso I y)
≃-transport {A} {B} {T₁} I x y p = record { eqProof = q }
    where
    T₂ =  iso-testable T₁ I
    f : A → B
    f = Iso.iso I
    g : B → A
    g = IsIso.inv (Iso.indeedIso I)
    o₁ = obs T₁
    o₂ = obs T₂
    lem : (a : A) → (o₂ ∘ f) a ≡ o₁ a
    lem a =
      begin
        (o₂ ∘ f) a
      ≡⟨ refl ⟩
        (o₁ ∘ g ∘ f) a
      ≡⟨ cong (λ x₁ → o₁ x₁) (IsIso.isLeftInv (Iso.indeedIso I) a) ⟩
        o₁ a
      ∎
    q : (φ : Test T₂) → f x ⊨ φ ≡ f y ⊨ φ
    q ⊤ = refl
    q ⊥ = refl
    q (nonTriv (nonTrivTest t)) =
      begin
        sat (kind T₂) t (o₂ (f x))
      ≡⟨ cong (λ u → sat (kind T₂) t u) (lem x) ⟩
        sat (kind T₂) t (o₁ x)
      ≡⟨ sat≡ (index T₁) (parts T₁) (kind T₁)
              o₂ (obsIso T₂) (partsTestable T₁) o₁ (obsIso T₁) lem p t ⟩
        sat (kind T₂) t (o₁ y)
      ≡⟨ cong (λ u → sat (kind T₂) t u) (sym $ lem y) ⟩
        sat (kind T₂) t (o₂ (f y))
      ∎
      where
        -- Agda complains at this point that
        -- T₁ != record { index = index T₁ ; parts = parts T₁ ; kind = kind T₁
        --              ; obs = obs T₁ ; obsIso = obsIso T₁
        --              ; partsTestable = partsTestable T₁}
        -- ...
        -- Is it possible to circumvent this issue?

        sat≡ : (Idx : Set) → (P : Idx → Set) → (k : Kind) →
               (o₂ : B → ObsTy Idx P k) → (isoT₂ : IsIso o₂) →
               (pTestable : (i : Idx) → Testable (P i)) →
               (o₁ : A → ObsTy Idx P k) → (isoT₁ : IsIso o₁) →
               ((a : A) → (o₂ ∘ f) a ≡ o₁ a) →
               x ≃〈 record
                  { index = Idx
                  ; parts = P
                  ; kind = k
                  ; obs = o₁
                  ; obsIso = isoT₁
                  ; partsTestable = pTestable
                  } 〉 y →
               (t' : SubTests
                     ( record
                      { index = Idx ; parts = P ; kind = k ; obs = o₂
                      ; obsIso = isoT₂ ; partsTestable = pTestable }) k ) →
               sat k t' (o₁ x) ≡ sat k t' (o₁ y)
        sat≡ = {!!}
-}

{-
≃-transport {A} {B} {T₁} I x y p =
  q (index T₁) (parts T₁) (kind T₁) (obs T₂) (obsIso T₂) (partsTestable T₁)
    (obs T₁) (obsIso T₁) lem {!!}
    -- Agda complains at this point that
    -- T₁ != record { index = index T₁ ; parts = parts T₁ ; kind = kind T₁
    --              ; obs = obs T₁ ; obsIso = obsIso T₁
    --              ; partsTestable = partsTestable T₁}
    -- ...
    -- Is it possible to circumvent this issue?
  where
    T₂ =  iso-testable T₁ I
    f : A → B
    f = Iso.iso I
    g : B → A
    g = IsIso.inv (Iso.indeedIso I)
    o₁ = obs T₁
    o₂ = obs T₂
    lem : (a : A) → (o₂ ∘ f) a ≡ o₁ a
    lem a =
      begin
        (o₂ ∘ f) a
      ≡⟨ refl ⟩
        (o₁ ∘ g ∘ f) a
      ≡⟨ cong (λ x₁ → o₁ x₁) (IsIso.isLeftInv (Iso.indeedIso I) a) ⟩
        o₁ a
      ∎

    q : (Idx : Set) → (P : Idx → Set) → (k : Kind) →
        (o₂ : B → ObsTy Idx P k) → (isoT₂ : IsIso o₂) →
        (pTestable : (i : Idx) → Testable (P i)) →
        (o₁ : A → ObsTy Idx P k) → (isoT₁ : IsIso o₁) →
        ((a : A) → (o₂ ∘ f) a ≡ o₁ a) →
        x ≃〈 record
                  { index = Idx
                  ; parts = P
                  ; kind = k
                  ; obs = o₁
                  ; obsIso = isoT₁
                  ; partsTestable = pTestable
                  } 〉 y →
        f x ≃〈 record
                  { index = Idx
                  ; parts = P
                  ; kind = k
                  ; obs = o₂
                  ; obsIso = isoT₂
                  ; partsTestable = pTestable
                  } 〉
        f y
    q Idx P ind o₂ isoT₂ pTestable o₁ isoT₁ lem p = record { eqProof = qi }
      where
        T₁' = record
          { index = Idx ; parts = P ; kind = ind
          ; obs = o₁ ; obsIso = isoT₁ ; partsTestable = pTestable }
        T₂' = record
          { index = Idx ; parts = P ; kind = ind
          ; obs = o₂ ; obsIso = isoT₂ ; partsTestable = pTestable }
        qi : (φ : Test T₂') → f x ⊨ φ ≡ f y ⊨ φ
        qi ⊤ = refl
        qi ⊥ = refl
        qi (nonTriv (nonTrivTest φs)) =
          begin
            cotuple (λ i z → z ⊨ app φs i) (o₂ (f x))
          ≡⟨ cong (λ u → cotuple (λ i z → z ⊨ app φs i) u) (lem x) ⟩
            cotuple (λ i z → z ⊨ app φs i) (o₁ x)
          ≡⟨ refl ⟩
            _⊨_ {A} {T₁'} x (nonTriv (nonTrivTest φs))
          ≡⟨ eqProof p (nonTriv (nonTrivTest φs)) ⟩
            _⊨_ {A} {T₁'} y (nonTriv (nonTrivTest φs))
          ≡⟨ refl ⟩
            cotuple (λ i z → z ⊨ app φs i) (o₁ y)
          ≡⟨ cong (λ u → cotuple (λ i z → z ⊨ app φs i) u) (sym $ lem y) ⟩
            cotuple (λ i z → z ⊨ app φs i) (o₂ (f y))
          ∎
    q Idx P coind o₂ isoT₂ pTestable o₁ isoT₁ lem p = record { eqProof = qc }
      where
        T₁' = record
          { index = Idx ; parts = P ; kind = coind
          ; obs = o₁ ; obsIso = isoT₁ ; partsTestable = pTestable }
        T₂' = record
          { index = Idx ; parts = P ; kind = coind
          ; obs = o₂ ; obsIso = isoT₂ ; partsTestable = pTestable }
        qc : (φ : Test T₂') → f x ⊨ φ ≡ f y ⊨ φ
        qc ⊤ = refl
        qc ⊥ = refl
        qc (nonTriv (nonTrivTest (i , φ))) =
          begin
            app (o₂ (f x)) i ⊨ φ
          ≡⟨ cong (λ u → app u i ⊨ φ) (lem x) ⟩
            app (o₁ x) i ⊨ φ
          ≡⟨ {!!} ⟩
            app (o₁ y) i ⊨ φ
          ≡⟨ cong (λ u → app u i ⊨ φ) (sym $ lem y) ⟩
            app (o₂ (f y)) i ⊨ φ
          ∎
-}
