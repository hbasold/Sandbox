-- | In this module, we proof that the 2-category of endofunctors
-- inherits locally all colimits from underlying category.
-- More precisely, for a functor F : C → C, we compute in Endo(F, F)
-- colimits point-wise from those in C.
module UpToColim where

open import Level
open import Relation.Binary using (Rel; IsEquivalence)
open import Data.Product
open import Categories.Support.Equivalence
open import Categories.Category
open import Categories.2-Category
open import Categories.Functor
open import Categories.NaturalTransformation
  renaming (id to natId; _≡_ to _≡N_; setoid to natSetoid)
  hiding (_∘ˡ_; _∘ʳ_)
open import Categories.Support.EqReasoning
open import Categories.Colimit
open import Categories.Cocones
open import Categories.Cocone
open import Categories.Object.Initial
open import Categories.Functor.Constant

open import UpTo

_⇒_ = NaturalTransformation

EndoDiagram : (C : Cat₀) → (F : EndoFunctor C) → (I : Cat₀) → Set
EndoDiagram C F I = Functor I (EndoMor (C , F) (C , F))

PW-Diagram : {C : Cat₀} → {F : EndoFunctor C} → {I : Cat₀} →
             EndoDiagram C F I → (X : Category.Obj C) →
             Functor I C
PW-Diagram {C} {F} {I} D X =
  record
  { F₀ = λ i → Functor.F₀ (Endo⇒.T (D.F₀ i)) X
  ; F₁ = λ h → NaturalTransformation.η (UpTo⇒.γ (D.F₁ h)) X
  ; identity = ≡U-proof D.identity
  ; homomorphism = ≡U-proof D.homomorphism
  ; F-resp-≡ = λ x → ≡U-proof (D.F-resp-≡ x)
  }
  where
    module C = Category C
    module D = Functor D
    module I = Category I
    open _≡U_


EndoMor-inherit-colim : {C : Cat₀} → (F : EndoFunctor C) →
                        {I : Cat₀} → (D : EndoDiagram C F I) →
                        ((X : Category.Obj C) → Colimit (PW-Diagram D X)) →
                        Colimit D
EndoMor-inherit-colim {C} F {I} D c =
  record
  { initial = record
    { ⊥ = colim-D
    ; ! = out
    ; !-unique = out-unique
    }
  }
  where
    -- Notations

    module C = Category C
    module I = Category I
    module CC-D = Category (Cocones D)

    -- Components of the diagram D
    D₀ = Functor.F₀ D
    D₁ = Functor.F₁ D

    -- Tᵢ(A) = D(i)(A)
    T : (i : I.Obj) → Functor C C
    T i = Endo⇒.T (D₀ i)

    -- Components of T
    T₀ = λ i → Functor.F₀ (T i)
    T₁ = λ i {A} {B} → Functor.F₁ (T i) {A} {B}

    -- The natural transformation (w/o proof) D(f) : D(i) ⇒ D(i)
    D₁η : ∀ {i j} → (f : I [ i , j ]) →
          (A : C.Obj) → C [ T₀ i A , T₀ j A ]
    D₁η f A = NaturalTransformation.η (UpTo⇒.γ (D₁ f)) A

    ----- Construction of the colimit -----
    -- It is given by the cocone (colim-T, ρ).

    -- Action of colim-T on objects
    colim-T₀ : C.Obj → C.Obj
    colim-T₀ A = CL.∃F
      where
        module CL = Colimit (c A)

    -- Injection into colim DX
    κ : (i : I.Obj) → (X : C.Obj) → C [ T₀ i X , Colimit.∃F (c X) ]
    κ i X = Colimit.Ic.ψ (c X) i

    -- Given a morphism u : A → B in C, we construct a cocone DA ⇒ colim DB,
    -- which will give us then T(u) by the universal property of colim DA.
    -- The components of the cocone are given by κBᵢ ∘ Tᵢ(u) : T₁(A) → colim DB,
    -- where we use that Tᵢ(A) = DA(i).
    cocone-T₁ : {A B : C.Obj} →
                C [ A , B ] → Category.Obj (Cocones (PW-Diagram D A))
    cocone-T₁ {A} {B} u = record
      { N = colim-T₀ B
      ; ψ = λ i → C [ κB i ∘ T₁ i u ]
      ; commute = comm
      }
      where
        module CA = Colimit (c A)
        module PW-Cocones-A = Category (Cocones (PW-Diagram D A))
        module CB = Colimit (c B)
        DA = PW-Diagram D A
        module DA = Functor DA
        DB = PW-Diagram D B
        module DB = Functor DB

        -- Injection into colim DB
        κB : (i : I.Obj) → C [ T₀ i B , CB.∃F ]
        κB i = NaturalTransformation.η CB.ι i

        .comm : {i j : I.Obj} (f : I [ i , j ]) →
                C [ κB i ∘ T₁ i u ] C.≡ C [ κB j ∘ T₁ j u ] C.∘ DA.F₁ f
        comm {i} {j} f =
          begin
            C [ κB i ∘ T₁ i u ]
          ↓⟨ C.∘-resp-≡
             (Colimit.Ic.commute (c B) f)
             C.Equiv.refl
          ⟩
            (κB j C.∘ DB.F₁ f) C.∘ T₁ i u
          ↓⟨ C.assoc ⟩
            κB j C.∘ (DB.F₁ f C.∘ T₁ i u)
          ↓⟨ C.∘-resp-≡
             C.Equiv.refl
             (NaturalTransformation.commute (UpTo⇒.γ (D₁ f)) u)
          ⟩
            κB j C.∘ (T₁ j u C.∘ DA.F₁ f)
          ↑⟨ C.assoc ⟩
            C [ κB j ∘ T₁ j u ] C.∘ DA.F₁ f
          ∎
          where
            open SetoidReasoning (C.hom-setoid {DA.F₀ i} {colim-T₀ B})

    -- Action of colim-T on morphisms
    colim-T₁ : {A B : C.Obj} → C [ A , B ] → C [ colim-T₀ A , colim-T₀ B ]
    colim-T₁ {A} {B} u = CoconeMorphism.f (CA.I.! {cocone-T₁ u})
      where
        module CA = Colimit (c A)

    -- Proof that T(id_A) = id_{T(A)}
    .colim-T-id : ∀ {A : C.Obj} →
                 C [ colim-T₁ (C.id {A}) ≡ C.id {colim-T₀ A} ]
    colim-T-id {A} = CA.I.⊥-id (record
        { f = colim-T₁ (C.id {A})
        ; commute = λ {i} →
          let open SetoidReasoning (C.hom-setoid {DA.F₀ i} {colim-T₀ A})
          in begin
            C [ colim-T₁ (C.id {A}) ∘ κ i A ]
          -- colimit property of T(id) = [κ i A ∘ id]_{i ∈ I}
          ↓⟨ CoconeMorphism.commute (CA.I.! {cocone-T₁ (C.id {A})}) ⟩
            C [ κ i A ∘ T₁ i (C.id {A}) ]
          -- Functoriality of Tᵢ
          ↓⟨ C.∘-resp-≡
             C.Equiv.refl
             (Functor.identity (T i))
          ⟩
            C [ κ i A ∘ C.id {T₀ i A} ]
          ↓⟨ C.identityʳ ⟩
            κ i A
          ∎
        })
      where
        module CA = Colimit (c A)
        module DA = Functor (PW-Diagram D A)

    -- Proof that T(g ∘ f) = Tg ∘ Tf
    .colim-T-hom : {X Y Z : C.Obj} {f : C [ X , Y ]} {g : C [ Y , Z ]} →
                   colim-T₁ (C [ g ∘ f ]) C.≡ C [ colim-T₁ g ∘ colim-T₁ f ]
    colim-T-hom {X} {Y} {Z} {f} {g} = CX.I.!-unique CX⇒TgTf
      where
        module CX = Colimit (c X)
        module CY = Colimit (c Y)
        module DX = Functor (PW-Diagram D X)
        module CC-DX = Category (Cocones (PW-Diagram D X))

        -- Show that Tg ∘ Tf is a cocone for T(g ∘ f), which implies that
        -- Tg ∘ Tf = T(g ∘ f).
        -- To achieve this, we need to show that for each i ∈ I, we have
        -- Tg ∘ Tf ∘ κ i X = κ i Z ∘ Tᵢ (g ∘ f).
        CX⇒TgTf : Colimit.I.⊥ (c X) CC-DX.⇒ cocone-T₁ (C [ g ∘ f ])
        CX⇒TgTf = record
          { f = C [ colim-T₁ g ∘ colim-T₁ f ]
          ; commute = λ {i : I.Obj} →
            let open SetoidReasoning (C.hom-setoid {DX.F₀ i} {colim-T₀ Z})
            in begin
               C [ colim-T₁ g ∘ colim-T₁ f ] C.∘ κ i X
            ↓⟨ C.assoc ⟩
                colim-T₁ g C.∘ (colim-T₁ f C.∘ κ i X)
            ↓⟨ C.∘-resp-≡
               C.Equiv.refl
               (CoconeMorphism.commute (CX.I.! {cocone-T₁ f}))
            ⟩
                colim-T₁ g C.∘ (κ i Y C.∘ T₁ i f)
            ↑⟨ C.assoc ⟩
                (colim-T₁ g C.∘ κ i Y) C.∘ T₁ i f
            ↓⟨ C.∘-resp-≡
               (CoconeMorphism.commute (CY.I.! {cocone-T₁ g}))
               C.Equiv.refl
            ⟩
                (κ i Z C.∘ T₁ i g) C.∘ T₁ i f
            ↓⟨ C.assoc ⟩
                κ i Z C.∘ (T₁ i g C.∘ T₁ i f)
            ↑⟨ C.∘-resp-≡
               C.Equiv.refl
               (Functor.homomorphism (T i))
            ⟩
              C [ κ i Z ∘ T₁ i (g C.∘ f) ]
            ∎
          }

    -- Proof that T respects the equality of C.
    .colim-T-resp-≡ : {A B : C.Obj} {f : C [ A , B ]} {g : C [ A , B ]} →
                      C [ f ≡ g ] → C [ colim-T₁ f ≡ colim-T₁ g ]
    colim-T-resp-≡ {A} {B} {f} {g} f≡g = CA.I.!-unique CA⇒Tg
      where
        module CA = Colimit (c A)
        module DA = Functor (PW-Diagram D A)
        module CC-DA = Category (Cocones (PW-Diagram D A))

        -- That T respects ≡ is inherited point-wise from the fact that
        -- each Tᵢ respects ≡.
        CA⇒Tg : Colimit.I.⊥ (c A) CC-DA.⇒ cocone-T₁ f
        CA⇒Tg = record
          { f = colim-T₁ g
          ; commute = λ {i} →
            let open SetoidReasoning (C.hom-setoid {DA.F₀ i} {colim-T₀ B})
            in begin
              C [ colim-T₁ g ∘ κ i A ]
            ↓⟨ CoconeMorphism.commute (CA.I.! {cocone-T₁ g}) ⟩
              C [ κ i B ∘ T₁ i g ]
            ↑⟨ C.∘-resp-≡
               C.Equiv.refl
               (Functor.F-resp-≡ (T i) f≡g)
            ⟩
              C [ κ i B ∘ T₁ i f ]
            ∎
          }


    -- The colimiting up-to technique
    colim-T : Functor C C
    colim-T = record
        { F₀ = colim-T₀
        ; F₁ = colim-T₁
        ; identity = colim-T-id
        ; homomorphism = colim-T-hom
        ; F-resp-≡ = colim-T-resp-≡
        }

    -- Natural transformation to make colim-T indeed an up-to technique
    colim-ρ : (colim-T ∘ F) ⇒ (F ∘ colim-T)
    colim-ρ = {!!}

    colim-D : CC-D.Obj
    colim-D =
      record
      { N = record
        { T = colim-T
        ; ρ = colim-ρ
        }
      ; ψ = {!!}
      ; commute = {!!}
      }

    out : ∀ {A : CC-D.Obj} → colim-D CC-D.⇒ A
    out = {!!}

    out-unique : {A : CC-D.Obj} (f : colim-D CC-D.⇒ A) → out CC-D.≡ f
    out-unique = {!!}
