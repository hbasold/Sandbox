module Common.Context (Ty : Set) where

open import Data.Nat as Nat
open import Data.List as List
import Level
open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import Relation.Binary using (Setoid)
open ≡-Reasoning
open import Function as Fun hiding (_∘′_)
open import Data.Sum as Sum hiding ([_,_])
open import Categories.Category using (Category)

open import Common.SumProperties

postulate
  η-≡ : {A : Set} {B : A → Set}
         {f₁ : (x : A) → B x}{f₂ : (y : A) → B y} →
         ((x : A) → f₁ x ≡ f₂ x) → f₁ ≡ f₂

-------------------------
---- Type contexts

Ctx = List Ty

-- | De Bruijn variable indexing
data Var : (Γ : Ctx) (a : Ty) → Set where
  zero : ∀{Γ a}                          → Var (a ∷ Γ) a
  succ : ∀{Γ b} (a : Ty) → (x : Var Γ a) → Var (b ∷ Γ) a

data _≅V_ : ∀{Γ Γ' : Ctx} {a a' : Ty} → Var Γ a → Var Γ' a' → Set where
  zero : ∀ {Γ Γ'} {a a'}
         → zero {Γ = Γ} {a} ≅V zero {Γ = Γ'} {a'}

  succ  : ∀ {Γ Γ'} {a a'}
          → ∀ {x : Var Γ a} {x' : Var Γ' a'} {b b' : Ty}
          → x ≅V x'
          → succ {b = b} a x ≅V succ {b = b'} a' x'

Vrefl : ∀ {Γ : Ctx} {a : Ty} {x : Var Γ a} → x ≅V x
Vrefl {x = zero}  = zero
Vrefl {x = succ _ t} = succ Vrefl

Vsym : ∀ {Γ Γ' a a'} {x : Var Γ a} {x' : Var Γ' a'} → x ≅V x' → x' ≅V x
Vsym zero      = zero
Vsym (succ [x]) = succ (Vsym [x])

Vtrans : ∀ {Γ Γ' Γ'' a a' a''} {x : Var Γ a} {x' : Var Γ' a'} {x'' : Var Γ'' a''}
       → x ≅V x' → x' ≅V x'' → x ≅V x''
Vtrans zero     zero      = zero
Vtrans (succ eq) (succ eq') = succ (Vtrans eq eq')

-- Note: makes the equality homogeneous in Γ and a
≅V-setoid : ∀ {Γ a} → Setoid _ _
≅V-setoid {Γ} {a} = record
  { Carrier = Var Γ a
  ; _≈_ = _≅V_
  ; isEquivalence = record
    { refl = Vrefl ; sym = Vsym ; trans = Vtrans }
  }

arr : (Γ Δ : Ctx) → Set
arr Γ Δ = ∀ (a : Ty) → Var Γ a → Var Δ a

_∘′_ : {Γ Δ Ξ : Ctx} (ρ : arr Δ Ξ) (γ : arr Γ Δ) → arr Γ Ξ
_∘′_ ρ γ = λ a x → ρ a (γ a x)

id′ : {Γ : Ctx} →  arr Γ Γ
id′ = λ _ x → x

comp-resp-≡ : ∀ {Γ Δ Ξ : Ctx} {ρ ρ' : arr Δ Ξ} {γ γ' : arr Γ Δ} →
              ρ ≡ ρ' → γ ≡ γ' → ρ ∘′ γ ≡ ρ' ∘′ γ'
comp-resp-≡ {Γ} {Δ} {Ξ} {ρ} {ρ'} {γ} {γ'} ρ≡ρ' γ≡γ' =
  begin
    ρ ∘′ γ
  ≡⟨ refl ⟩
    (λ a x → ρ a (γ a x))
  ≡⟨ cong (λ u → (λ a x → ρ a (u a x))) γ≡γ' ⟩
    (λ a x → ρ a (γ' a x))
  ≡⟨ cong (λ u → (λ a x → u a (γ' a x))) ρ≡ρ' ⟩
    (λ a x → ρ' a (γ' a x))
  ≡⟨ refl ⟩
    (ρ' ∘′ γ')
  ∎

-- | Contexts form a category
ctx-cat : Category Level.zero Level.zero Level.zero
ctx-cat = record
   { Obj = Ctx
   ; _⇒_ = arr
   ; _≡_ = PE._≡_
   ; _∘_ = _∘′_
   ; id = id′
   ; assoc = refl
   ; identityˡ = refl
   ; identityʳ = refl
   ; equiv = PE.isEquivalence
   ; ∘-resp-≡ = comp-resp-≡
   }

open Categories.Category.Category ctx-cat
  renaming ( _⇒_ to _▹_
           ; _≡_ to _≈_
           ; _∘_ to _●_
           ; id  to ctx-id
           )

-------------------------
---- Coproduct structure on contexts

_⊕_ : Ctx → Ctx → Ctx
Γ₁ ⊕ Γ₂ = Γ₁ ++ Γ₂

in₁ : {Γ₁ Γ₂ : Ctx} → Γ₁ ▹ (Γ₁ ⊕ Γ₂)
in₁ _ zero     = zero
in₁ a (succ .a x) = succ a (in₁ a x)

in₂ : {{Γ₁ Γ₂ : Ctx}} → Γ₂ ▹ (Γ₁ ⊕ Γ₂)
in₂ {{[]}}     _ x = x
in₂ {{b ∷ Γ₁}} a x = succ a (in₂ a x)

split : {Γ₁ Γ₂ : Ctx} {a : Ty} → Var (Γ₁ ⊕ Γ₂) a → Var Γ₁ a ⊎ Var Γ₂ a
split {[]}      {Γ₂}     x        = inj₂ x
split {a ∷ Γ₁'} {Γ₂}     zero     = inj₁ zero
split {b ∷ Γ₁'} {Γ₂} {a} (succ .a y) = (Sum.map (succ a) (ctx-id a)) (split {Γ₁'} y)

[_,_] : {Γ₁ Γ₂ Δ : Ctx} (f : Γ₁ ▹ Δ) (g : Γ₂ ▹ Δ)
      → ((Γ₁ ⊕ Γ₂) ▹ Δ)
[_,_] {Γ} {Γ₂} f g a x = ([ f a , g a ]′) (split x)

_-⊕-_ : {Γ Γ₂ Γ' Γ₂' : Ctx} (f : Γ ▹ Γ') (g : Γ₂ ▹ Γ₂')
      → ((Γ ⊕ Γ₂) ▹ (Γ' ⊕ Γ₂'))
_-⊕-_ {Γ} {Γ₂} {Γ'} {Γ₂'} f g = [ in₁ ● f , in₂ {{Γ'}} {{Γ₂'}} ● g ]


succ-distr-lemma : {Γ : Ctx} {a b : Ty} (Γ₂ : Ctx) (x : Var Γ a) →
                   (in₁ {b ∷ Γ} ● succ {Γ}) a x
                   ≡ (succ {Γ ⊕ Γ₂} ● in₁ {Γ} {Γ₂}) a x
succ-distr-lemma Γ₂ x = refl

split-lemma₁ : {a : Ty} (Γ₁ Γ₂ : Ctx) (x : Var Γ₁ a) →
               split {Γ₁} {Γ₂} (in₁ {Γ₁} a x) ≡ inj₁ x
split-lemma₁ (tt ∷ Γ₁) Γ₂ zero       = refl
split-lemma₁ (tt ∷ Γ₁) Γ₂ (succ a x) =
  begin
    split {tt ∷ Γ₁} (in₁ {tt ∷ Γ₁} a (succ a x))
  ≡⟨ refl ⟩
    (Sum.map (succ a) id) (split (in₁ a x))
  ≡⟨ cong (Sum.map (succ a) id) (split-lemma₁ Γ₁ Γ₂ x) ⟩
    (Sum.map (succ a) id) (inj₁ x)
  ≡⟨ refl ⟩
    inj₁ (succ a x)
  ∎

split-lemma₂ : {a : Ty} (Γ₁ Γ₂ : Ctx) (x : Var Γ₂ a) →
               split {Γ₁} {Γ₂} (in₂ a x) ≡ inj₂ x
split-lemma₂ [] Γ₂ x = refl
split-lemma₂ {a} (tt ∷ Γ₁) Γ₂ x =
  begin
    split {tt ∷ Γ₁} {Γ₂} (in₂ {{tt ∷ Γ₁}} a x)
  ≡⟨ refl ⟩
    Sum.map (succ a) id (split (in₂ {{Γ₁}} a x))
  ≡⟨ cong (λ u → Sum.map (succ a) id u) (split-lemma₂ Γ₁ Γ₂ x) ⟩
    Sum.map (succ a) id (inj₂ x)
  ≡⟨ refl ⟩
    inj₂ x
  ∎

split-lemma : (Γ₁ Γ₂ : Ctx) (a : Ty) (x : Var (Γ₁ ⊕ Γ₂) a) →
             [ in₁ {Γ₁} {Γ₂} a , in₂ a ]′ (split x) ≡ x
split-lemma []       Γ₂ _  x           = refl
split-lemma (a ∷ Γ₁) Γ₂ .a zero        = refl
split-lemma (b ∷ Γ₁) Γ₂ a  (succ .a x) =
  begin
    [ in₁ {b ∷ Γ₁} a , in₂ {{b ∷ Γ₁}} a ]′ (split (succ a x))
  ≡⟨ refl ⟩
    [ in₁ {b ∷ Γ₁} a , (succ {Γ₁ ⊕ Γ₂} ● in₂ {{Γ₁}} ) a ]′
      (Sum.map (succ {Γ₁} a) id (split x))
  ≡⟨ copair-sum-map-merge {f₁ = Var.succ {Γ₁} {b} a} (split x) ⟩
    [ (in₁ {b ∷ Γ₁} ● succ {Γ₁}) a , (succ {Γ₁ ⊕ Γ₂} ● in₂) a ]′ (split x)
  ≡⟨ copair-cong {f = (in₁ {b ∷ Γ₁} ● succ {Γ₁}) a}
                 (succ-distr-lemma Γ₂)
                 (split x) ⟩
    [ (succ {Γ₁ ⊕ Γ₂} ● in₁ {Γ₁}) a , (succ {Γ₁ ⊕ Γ₂} ● in₂) a ]′ (split x)
  ≡⟨ copair-distr {f = in₁ {Γ₁} {Γ₂} a} {h = succ {Γ₁ ⊕ Γ₂} a} (split x)⟩
    (Var.succ {Γ₁ ⊕ Γ₂} {b} a ∘ [ in₁ {Γ₁} a , in₂ a ]′) (split x)
  ≡⟨ cong (succ {Γ₁ ⊕ Γ₂} {b} a) (split-lemma Γ₁ Γ₂ a x) ⟩
     succ {Γ₁ ⊕ Γ₂} a x
  ∎

⊕-is-coprod-arg : ∀{Γ₁ Γ₂ : Ctx} (a : Ty) (x : Var (Γ₁ ⊕ Γ₂) a) →
                  [ in₁ {Γ₁} {Γ₂} , in₂ ] a x ≡ ctx-id a x
⊕-is-coprod-arg {Γ₁} {Γ₂} = split-lemma Γ₁ Γ₂

⊕-is-coprod : ∀{Γ₁ Γ₂ : Ctx} → [ in₁ {Γ₁} {Γ₂} , in₂ ] ≡ ctx-id
⊕-is-coprod {Γ₁} =
  η-≡ {f₁ = [ in₁ {Γ₁} , in₂ ]}
      {f₂ = ctx-id}
      (λ (a : Ty) →
        η-≡ {f₁ = [ in₁ {Γ₁}, in₂ ] a}
            {f₂ = ctx-id a}
            (⊕-is-coprod-arg {Γ₁} a)
       )

●-distr-copair₁ˡ : ∀{Γ₁ Γ₂ Δ : Ctx}
                   (h : (Γ₁ ⊕ Γ₂) ▹ Δ) (a : Ty) (x : Var (Γ₁ ⊕ Γ₂) a) →
                   [ h ● in₁ {Γ₁} {Γ₂} , h ● in₂ {{Γ₁}} {{Γ₂}} ] a x
                   ≡ (h ● [ in₁ {Γ₁} {Γ₂} , in₂ ]) a x
●-distr-copair₁ˡ {Γ₁} {Γ₂} {Δ} h a x =
  begin
    [ h ● in₁ {Γ₁} , h ● in₂ ] a x
  ≡⟨ refl ⟩
    ([ (h ● in₁ {Γ₁}) a , (h ● in₂) a ]′) (split x)
  ≡⟨ copair-distr {f = in₁ {Γ₁} a} {g = in₂ a} {h = h a} (split x) ⟩
    (h ● [ in₁ {Γ₁} , in₂ ]) a x
  ∎

●-distr-copairˡ : ∀{Γ₁ Γ₂ Δ : Ctx} (h : (Γ₁ ⊕ Γ₂) ▹ Δ) →
                 [ h ● in₁ {Γ₁} {Γ₂} , h ● in₂ {{Γ₁}} {{Γ₂}} ]
                 ≡ h ● [ in₁ {Γ₁} {Γ₂} , in₂ ]
●-distr-copairˡ {Γ₁} h = η-≡ (λ a → η-≡ (●-distr-copair₁ˡ {Γ₁} h a))

⊕-is-coprod₁ : ∀{Γ₁ Γ₂ Δ : Ctx} {f : Γ₁ ▹ Δ} {g : Γ₂ ▹ Δ} {h : (Γ₁ ⊕ Γ₂) ▹ Δ} →
               h ● in₁ ≡ f → h ● in₂ ≡ g → [ f , g ] ≡ h
⊕-is-coprod₁ {Γ₁} {Γ₂} {Δ} {f} {g} {h} h●in₁≡f h●in₂≡g =
  begin
    [ f , g ]
  ≡⟨ cong (λ u → [ u , g ]) (sym h●in₁≡f) ⟩
    [ h ● in₁ {Γ₁} , g ]
  ≡⟨ cong (λ u → [ h ● in₁ {Γ₁} , u ]) (sym h●in₂≡g) ⟩
    [ h ● in₁ {Γ₁} , h ● in₂ ]
  ≡⟨ ●-distr-copairˡ {Γ₁} h ⟩
    h ● [ in₁ {Γ₁}, in₂ ]
  ≡⟨ cong (λ u → h ● u) (⊕-is-coprod {Γ₁}) ⟩
    h ● ctx-id
  ≡⟨ refl ⟩
    h
  ∎

commute-in₁-arg : ∀ {Γ₁ Γ₂ Δ : Ctx} {f : Γ₁ ▹ Δ} {g : Γ₂ ▹ Δ}
                    (a : Ty) (x : Var Γ₁ a) →
                  ([ f , g ] ● in₁) a x ≡ f a x
commute-in₁-arg _ zero = refl
commute-in₁-arg {b ∷ Γ₁} {Γ₂} {Δ} {f} {g} a (succ .a x) =
  begin
    ([ f , g ] ● in₁ {b ∷ Γ₁}) a (succ {Γ₁} a x)
  ≡⟨ refl ⟩
    [ f , g ] a (succ {Γ₁ ⊕ Γ₂} a (in₁ {Γ₁} a x))
  ≡⟨ refl ⟩
    ([ f a , g a ]′) (split (succ {Γ₁ ⊕ Γ₂} a (in₁ {Γ₁} a x)))
  ≡⟨ refl ⟩
    [ f a , g a ]′ ((Sum.map (succ a) id) (split {Γ₁} {Γ₂} (in₁ {Γ₁} a x)))
  ≡⟨ refl ⟩
    (([ f a , g a ]′ ∘ (Sum.map (succ a) id)) (split {Γ₁} {Γ₂} (in₁ {Γ₁} a x)))
  ≡⟨ copair-sum-map-merge {f₁ = succ a} (split {Γ₁} {Γ₂} (in₁ {Γ₁} a x)) ⟩
    ([ (f ● succ) a , g a ]′ (split {Γ₁} {Γ₂} (in₁ {Γ₁} a x)))
  ≡⟨ cong ([ (f ● succ) a , g a ]′) (split-lemma₁ Γ₁ Γ₂ x) ⟩
    f a (succ a x)
  ∎

commute-in₁ : {Γ₁ Γ₂ Δ : Ctx} {f : Γ₁ ▹ Δ} {g : Γ₂ ▹ Δ} → [ f , g ] ● in₁ ≈ f
commute-in₁ {Γ₁} {Γ₂} {Δ} {f} {g} =
  η-≡ {f₁ = [ f , g ] ● in₁}
      {f₂ = f}
      (λ a → η-≡ {f₁ = ([ f , g ] ● in₁) a}
                 {f₂ = f a}
                 (commute-in₁-arg {f = f} {g = g} a)
      )

commute-in₂-arg : ∀ {Γ₁ Γ₂ Δ : Ctx} {f : Γ₁ ▹ Δ} {g : Γ₂ ▹ Δ}
                    (a : Ty) (x : Var Γ₂ a) →
                  ([ f , g ] ● in₂) a x ≡ g a x
commute-in₂-arg {[]} _ _ = refl
commute-in₂-arg {tt ∷ Γ₁} {Γ₂} {Δ} {f} {g} a x =
  begin
    ([ f , g ] ● in₂ {{tt ∷ Γ₁}} ) a x
  ≡⟨ refl ⟩
    [ f , g ] a ((succ ● in₂) a x)
  ≡⟨ refl ⟩
    [ f a , g a ]′ (split {tt ∷ Γ₁} (succ a (in₂ a x)))
  ≡⟨ cong (λ u → [ f a , g a ]′ u) {x = split {tt ∷ Γ₁} (succ a (in₂ a x))} refl ⟩
    [ f a , g a ]′ ((Sum.map (succ a) id) (split {Γ₁} (in₂ a x)))
  ≡⟨ cong (λ u → [ f a , g a ]′ (Sum.map (succ a) id u)) (split-lemma₂ Γ₁ Γ₂ x) ⟩
    [ f a , g a ]′ ((Sum.map (succ a) id) (inj₂ x))
  ≡⟨ copair-sum-map-merge {f₁ = succ {Γ₁} a} {f₂ = id} {g₁ = f a} {g₂ = g a} (inj₂ x) ⟩
    [ (f ● succ) a , (g ● ctx-id) a ]′ (inj₂ x)
  ≡⟨ copair-elimʳ {f = (f ● succ) a} {g = (g ● ctx-id) a} x ⟩
    g a x
  ∎

commute-in₂ : {Γ₁ Γ₂ Δ : Ctx} {f : Γ₁ ▹ Δ} {g : Γ₂ ▹ Δ} → [ f , g ] ● in₂ ≈ g
commute-in₂ {Γ₁} {Γ₂} {Δ} {f} {g} =
  η-≡ {f₁ = [ f , g ] ● in₂}
      {f₂ = g}
      (λ a → η-≡ {f₁ = ([ f , g ] ● in₂) a}
                 {f₂ = g a}
                 (commute-in₂-arg {f = f} {g = g} a)
      )

open import Categories.Object.Coproduct ctx-cat

ctx-coproduct : ∀{Γ₁ Γ₂ : Ctx} → Coproduct Γ₁ Γ₂
ctx-coproduct {Γ₁} {Γ₂} = record
                  { A+B = Γ₁ ⊕ Γ₂
                  ; i₁ = in₁
                  ; i₂ = in₂
                  ; [_,_] = [_,_]
                  ; commute₁ = commute-in₁
                  ; commute₂ = commute-in₂
                  ; universal = ⊕-is-coprod₁
                  }

open import Categories.Object.BinaryCoproducts ctx-cat

ctx-bin-coproducts : ∀{Γ₁ Γ₂ : Ctx} → BinaryCoproducts
ctx-bin-coproducts = record { coproduct = ctx-coproduct }

open BinaryCoproducts ctx-bin-coproducts
