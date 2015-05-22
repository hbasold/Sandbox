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

    -- Action of colim-T on morphisms
    colim-T₁ : {A B : C.Obj} → C [ A , B ] → C [ colim-T₀ A , colim-T₀ B ]
    colim-T₁ {A} {B} u = CA.< κDuNat >
      where
        module CA = Colimit (c A)
        module CB = Colimit (c B)
        DA = PW-Diagram D A
        module DA = Functor DA
        DB = PW-Diagram D B
        module DB = Functor DB

        -- Injection into colim DB
        κB : (i : I.Obj) → C [ T₀ i B , CB.∃F ]
        κB i = NaturalTransformation.η CB.ι i

        -- The components of the morphism we construct are given by
        -- κBᵢ ∘ Tᵢ(u), giving us, see above, by the colimit property a
        -- morphism [κBᵢ ∘ Tᵢ(u)]_{i ∈ I} : colim DA → colim DB.
        κDuNat : NaturalTransformation DA (Constant (colim-T₀ B))
        κDuNat = record
          { η = λ i → C [ κB i ∘ T₁ i u ]
          ; commute = comm
          }
          where
            .comm : ∀ {i j} → (f : I [ i , j ]) →
              C.CommutativeSquare
              (DA.F₁ f)              (C [ κB i ∘ T₁ i u ])
              (C [ κB j ∘ T₁ j u ])  (C.id {colim-T₀ B})
            comm {i} {j} f =
              begin
                C [ (C [ κB j ∘ T₁ j u ]) ∘ DA.F₁ f ]
              ↓⟨ C.assoc ⟩
                C [ κB j ∘ C [ T₁ j u ∘ DA.F₁ f ] ]
              ↓⟨ C.Equiv.refl ⟩
                C [ κB j ∘ C [ T₁ j u ∘ (D₁η f) A ] ]
              -- D₁ f : Tᵢ ⇒ Tⱼ natural
              ↑⟨ C.∘-resp-≡
                 C.Equiv.refl
                 (NaturalTransformation.commute (UpTo⇒.γ (D₁ f)) u)
              ⟩
                C [ κB j ∘ C [ (D₁η f) B ∘ T₁ i u ] ]
              ↑⟨ C.Equiv.refl ⟩
                C [ κB j ∘ C [ DB.F₁ f ∘ T₁ i u ] ]
              ↑⟨ C.assoc ⟩
                C [ C [ κB j ∘ DB.F₁ f ] ∘ T₁ i u ]
              -- CB is colimit
              ↓⟨ C.∘-resp-≡
                 (NaturalTransformation.commute CB.ι f)
                 C.Equiv.refl
              ⟩
                C [ C [ C.id {colim-T₀ B} ∘ κB i ] ∘ T₁ i u ]
              ↓⟨ C.assoc ⟩
                C [ C.id {colim-T₀ B} ∘ (C [ κB i ∘ T₁ i u ]) ]
              ∎
              where
                open SetoidReasoning (C.hom-setoid {DA.F₀ i} {colim-T₀ B})


    colim-T : Functor C C
    colim-T = record
        { F₀ = colim-T₀
        ; F₁ = colim-T₁
        ; identity = {!!}
        ; homomorphism = {!!}
        ; F-resp-≡ = {!!}
        }

    colim-D : CC-D.Obj
    colim-D =
      record
      { N = record
        { T = colim-T
        ; ρ = {!!}
        }
      ; ψ = {!!}
      ; commute = {!!}
      }

    out : ∀ {A : CC-D.Obj} → colim-D CC-D.⇒ A
    out = {!!}

    out-unique : {A : CC-D.Obj} (f : colim-D CC-D.⇒ A) → out CC-D.≡ f
    out-unique = {!!}
