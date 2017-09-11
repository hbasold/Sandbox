open import Signature

-- | In this module, we construct the free monad and the free completely
-- iterative monad over a signature Σ (see Aczel, Adamek, Milius and Velebil).
-- The first assigns to a set V of variables the set TV of finite terms over Σ
-- (that is, finite trees labelled with symbols in f ∈ ∥Σ∥ and ar(f) branching).
-- The second extends this to also allow for infinite trees, the set of those
-- is then denoted by T∞(V).
-- Categorically, T(V) is the initial (Σ + V)-algebra, whereas T∞(V) is the
-- final (Σ + V)-coalgebra.
module Terms (Σ : Sig) where

open import Function
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Product as Prod renaming (Σ to ⨿)
open import Data.Nat as Nat
open import Data.Sum as Sum
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Relation.Binary hiding (_⇒_)
open import Relation.Unary hiding (_⇒_)
import Streams as Str
open import Streams hiding (corec)

-- | Natural transformations
Nat : (Set → Set) → (Set → Set) → Set₁
Nat F G = ∀{X} → F X → G X

Id : Set → Set
Id = id

least : {X : Set} (_⊑_ : Rel X _) (P : X → Set) → X → Set
least _⊑_ P x = (P x) × (∀ {y} → P y → x ⊑ y)

least-unique : {X : Set} {_⊑_ : Rel X _} → (IsTotalOrder _≡_ _⊑_) →
               {P : X → Set} → (x y : X) → least _⊑_ P x → least _⊑_ P y → x ≡ y
least-unique isTO x y (p , l₁) (q , l₂) with IsTotalOrder.total isTO x y
least-unique isTO x y (p , l₁) (q , l₂) | inj₁ x⊑y =
  IsTotalOrder.antisym isTO x⊑y (l₂ p)
least-unique isTO x y (p , l₁) (q , l₂) | inj₂ y⊑x =
  IsTotalOrder.antisym isTO (l₁ q) y⊑x

infixr 1 _⇒_
_⇒_ = Nat

data T (V : Set) : Set where
  sup : ⟪ Σ ⟫ (T V) ⊎ V → T V

rec : ∀{V X} → (f : ⟪ Σ ⟫ X ⊎ V → X) → T V → X
rec f (sup (inj₁ (s , α))) = f (inj₁ (s , λ i → rec f (α i)))
rec f (sup (inj₂ y))       = f (inj₂ y)

rec-hom : ∀{V X} → (f : ⟪ Σ ⟫ X ⊎ V → X) (u : ⟪ Σ ⟫ (T V) ⊎ V) →
          rec f (sup u) ≡ f (Sum.map (⟪ Σ ⟫₁ (rec f)) id u)
rec-hom f (inj₁ (s , α)) = cong (λ u → f (inj₁ (s , u))) refl
rec-hom f (inj₂ v) = refl

-- | Functor T, on morphisms
T₁ : ∀ {V W} → (V → W) → T V → T W
T₁ f = rec (sup ∘ Sum.map id f)

η : Id ⇒ T
η = sup ∘ inj₂

μ : T ∘ T ⇒ T
μ {V} = rec f
  where
    f : ⟪ Σ ⟫ (T V) ⊎ T V → T V
    f = [ sup ∘ inj₁ , id ]

-- | First monad law
postulate unitᵣ : ∀{V} {t : T V} → μ (T₁ η t) ≡ t
{-
unitᵣ {V} {t} =
  begin
    μ (T₁ η t)
  ≡⟨ {!!} ⟩
    t
  ∎
-}

-- | T is free over Σ with inclusion
ι : ⟪ Σ ⟫ ⇒ T
ι = sup ∘ inj₁ ∘ ⟪ Σ ⟫₁ η

postulate T₁-top-sym : ∀{V W} (f : V → W) (s : ∥ Σ ∥) (α : ar Σ s → T V) →
             T₁ f (μ (ι (s , α))) ≡ μ (ι (s , T₁ f ∘ α))
-- T₁-top-sym = {!!}

-- | Kleisli morphsims for T∞ V
Subst : Set → Set → Set
Subst V W = V → T W

infixr 9 _•_

-- | Kleisli composition
_•_ : ∀ {U V W} → Subst V W → Subst U V → Subst U W
τ • σ = μ ∘ T₁ τ ∘ σ

-- | Application of substitutions to infinite terms
app : ∀ {V W} → Subst V W → T V → T W
app σ = μ ∘ T₁ σ

infixl 1 _≡ₛ_

_≡ₛ_ : ∀{V W} → Rel (Subst V W) _
σ ≡ₛ τ = ∀ {v} → σ v ≡ τ v

-- | Order on subsitutions
_⊑_ : ∀{V W} → Rel (Subst V W) _
σ₁ ⊑ σ₂ = ∃ λ σ → σ • σ₁ ≡ₛ σ₂

matches : ∀{V W} → T V → T W → Subst V W → Set
matches t s σ = app σ t ≡ s

-- | Most general matcher
mgm : ∀{V W} → T V → T W → Subst V W → Set
mgm t s = least _⊑_ (matches t s)

η-mgm : ∀{V} (t : T V) → mgm t t η
η-mgm {V} t = m , min t
  where
    m : matches t t η
    m =
      begin
        app η t
      ≡⟨ refl ⟩
        μ (T₁ η t)
      ≡⟨ unitᵣ ⟩
        t
      ∎

    min : {σ : Subst V V} (t : T V) → matches t t σ → η ⊑ σ
    min {σ} t m with app σ t
    min {σ} (sup (inj₁ y)) refl | sup (inj₁ .y) = σ , refl
    min (sup (inj₁ x)) () | sup (inj₂ w)
    min (sup (inj₂ v)) () | sup (inj₁ y)
    min {σ} (sup (inj₂ v)) refl | sup (inj₂ .v) = σ , refl

unifies : ∀{V W} → T V → T V → Subst V W → Set
unifies t s σ = app σ t ≡ app σ s

-- | Most general unifier
mgu : ∀{V W} → T V → T V → Subst V W → Set
mgu t s = least _⊑_ (unifies t s)

-- | Free variables
fv : ∀{V} → T V → Pred V _
fv (sup (inj₁ (s , α))) v = ⨿ (Sig.ar Σ s) λ i → (fv (α i) v)
fv (sup (inj₂ v₁))      v = v₁ ≡ v

isCons : ∀{V} → Pred (T V) _
isCons (sup (inj₁ x)) = ⊤
isCons (sup (inj₂ y)) = ⊥

isVar : ∀{V} → Pred (T V) _
isVar (sup (inj₁ x)) = ⊥
isVar (sup (inj₂ y)) = ⊤

record T∞ (V : Set) : Set where
  coinductive
  field out : ⟪ Σ ⟫ (T∞ V) ⊎ V
open T∞ public

sum-lift : {A B : Set} (R₁ : A → A → Set) (R₂ : B → B → Set) (x y : A ⊎ B) → Set
sum-lift R₁ R₂ (inj₁ x) (inj₁ y) = R₁ x y
sum-lift R₁ R₂ (inj₁ x) (inj₂ y) = ⊥
sum-lift R₁ R₂ (inj₂ x) (inj₁ y) = ⊥
sum-lift R₁ R₂ (inj₂ x) (inj₂ y) = R₂ x y

~-data : ∀{V} (R : T∞ V → T∞ V → Set) (u w : ⟪ Σ ⟫ (T∞ V) ⊎ V) → Set
~-data R = sum-lift (sig-lift R) _≡_

record _~_ {V : Set} (t s : T∞ V) : Set where
  coinductive
  field out~ : ~-data _~_ (out t) (out s)
open _~_ public

corec : ∀{V X} → (f : X → ⟪ Σ ⟫ X ⊎ V) → X → T∞ V
out (corec f x) with f x
... | inj₁ (s , α) = inj₁ (s , (λ i → corec f (α i)))
... | inj₂ v       = inj₂ v

prim-corec : ∀{V X} → (f : X → ⟪ Σ ⟫ X ⊎ V ⊎ T∞ V) → X → T∞ V
out (prim-corec {V} {X} f x) with f x
... | inj₁ (s , α)  = inj₁ (s , (λ i → prim-corec f (α i)))
... | inj₂ (inj₁ v) = inj₂ v
... | inj₂ (inj₂ t) = out t

sup∞ : ∀{V} → ⟪ Σ ⟫ (T∞ V) ⊎ V → T∞ V
out (sup∞ (inj₁ u)) = inj₁ u
out (sup∞ (inj₂ v)) = inj₂ v

-- | Functor T∞, on morphisms
T∞₁ : ∀ {V W} → (V → W) → T∞ V → T∞ W
T∞₁ f = corec (Sum.map id f ∘ out)

η∞ : Id ⇒ T∞
η∞ = sup∞ ∘ inj₂

μ∞ : T∞ ∘ T∞ ⇒ T∞
μ∞ {V} = corec f
  where
    g : T∞ V → ⟪ Σ ⟫ (T∞ (T∞ V)) ⊎ V
    g = Sum.map (⟪ Σ ⟫₁ η∞) id ∘ out

    f : T∞ (T∞ V) → ⟪ Σ ⟫ (T∞ (T∞ V)) ⊎ V
    f = [ inj₁ , g ] ∘ out

ι∞ : ⟪ Σ ⟫ ⇒ T∞
ι∞ {V} = g ∘ inj₁
  where
    g : ⟪ Σ ⟫ V ⊎ T∞ V → T∞ V
    g = prim-corec [ inj₁ ∘ ⟪ Σ ⟫₁ (inj₂ ∘ η∞) , inj₂ ∘ inj₂ ]

-- | T is a submonad of T∞
χ : T ⇒ T∞
χ = rec sup∞

-- | Kleisli morphsims for T∞ V
Subst∞ : Set → Set → Set
Subst∞ V W = V → T∞ W

infixl 1 _≡ₛ∞_

_≡ₛ∞_ : ∀{V W} → Rel (Subst∞ V W) _
σ ≡ₛ∞ τ = ∀ {v} → σ v ~ τ v

infixr 9 _•∞_

-- | Kleisli composition
_•∞_ : ∀ {U V W} → Subst∞ V W → Subst∞ U V → Subst∞ U W
τ •∞ σ = μ∞ ∘ T∞₁ τ ∘ σ

-- | Application of substitutions to infinite terms
app∞ : ∀ {V W} → Subst∞ V W → T∞ V → T∞ W
app∞ σ = μ∞ ∘ T∞₁ σ

isVar∞ : ∀{V} → Pred (T∞ V) _
isVar∞ t with out t
isVar∞ t | inj₁ x = ⊥
isVar∞ t | inj₂ v = ⊤

varNowOrLater : ∀{V} → (T∞ V → Pred V _) → T∞ V → Pred V _
varNowOrLater R t v with out t
... | inj₁ (f , α) = ∃ (λ i → R (α i) v)
... | inj₂ v₁      = v ≡ v₁

record fv∞ {V : Set} (t : T∞ V) (v : V) : Set where
  coinductive
  field isFv∞ : varNowOrLater fv∞ t v

root-matches : ∀{V} → T V → ∥ Σ ∥ → Set
root-matches (sup (inj₁ (g , _))) f = g ≡ f
root-matches (sup (inj₂ y))       f = ⊥

record RootsMatch {V : Set} (s : Stream (T V)) (f : ∥ Σ ∥) : Set where
  coinductive
  field
    hd-match : root-matches (hd s) f
    tl-match : RootsMatch (tl s) f
open RootsMatch

-- | Nasty hack: assume that RootsMatch is propositional
postulate
  RootsMatch-unique : ∀{V} {s : Stream (T V)} {f : ∥ Σ ∥}
                      (p q : RootsMatch s f) → p ≡ q

split : {V : Set} (s : Stream (T V)) (f : ∥ Σ ∥) → RootsMatch s f →
        ar Σ f → Stream (T V)
hd (split s f p i) with hd s | hd-match p
hd (split s f p i) | sup (inj₁ (.f , α)) | refl = α i
hd (split s f p i) | sup (inj₂ y) | ()
tl (split s f p i) = split (tl s) f (tl-match p) i

root-matches∞ : ∀{V} → T∞ V → ∥ Σ ∥ → Set
root-matches∞ t f with out t
root-matches∞ t f | inj₁ (g , _) = f ≡ g
root-matches∞ t f | inj₂ v       = ⊥

split∞ : {V : Set} → (t : T∞ V) (f : ∥ Σ ∥) → root-matches∞ t f →
        ar Σ f → T∞ V
split∞ t f p i with out t
split∞ t f refl i | inj₁ (.f , α) = α i
split∞ t f ()   i | inj₂ y

data AnyRootMatch {V : Set} (s : Stream (T V)) (f : ∥ Σ ∥) : Stream (T V) → Set where
  match-hd : root-matches (hd s) f → AnyRootMatch s f s
  match-tl : AnyRootMatch (tl s) f (tl s) → AnyRootMatch s f (tl s)

first-root-match : ∀{V} → Stream (T V) → ∥ Σ ∥ → ℕ → Set
first-root-match s f = least _≤_ (λ k → root-matches (s at k) f)

conv-branch : {V : Set} (R : Stream (T V) → T∞ V → Set) →
               Stream (T V) → T∞ V → T V → ⟪ Σ ⟫ (T∞ V) ⊎ V → Set
conv-branch R s t (sup (inj₁ (f , α))) (inj₁ (g , β)) =
  ⨿ (f ≡ g) λ p →
  ⨿ (RootsMatch (tl s) f) λ q →
  ∀ i → R (split (tl s) f q i) (β (subst (ar Σ) p i))
conv-branch R s t (sup (inj₁ (f , α))) (inj₂ v) = ⊥
conv-branch R s t (sup (inj₂ v)) (inj₁ (f , α)) =
  ∃ λ s' → AnyRootMatch s f s' × R s' t
conv-branch R s t (sup (inj₂ v)) (inj₂ w) = v ≡ w × R (tl s) t

-- | A sequence s of finite terms converges to a possibly infinite term,
-- if for all i, sᵢ₊₁ = sᵢ[σ] for some substitution σ : V → T V and t = sᵢ[τ]
-- for some τ : V → T∞ V.
-- Note that this coincides with convergence in the prefix metric.
record _→∞_ {V : Set} (s : Stream (T V)) (t : T∞ V) : Set where
  coinductive
  field
    conv-out : conv-branch _→∞_ s t (hd s) (out t)
open _→∞_ public

{-
unique-conv : ∀{V} (s : Stream (T V)) (t₁ t₂ : T∞ V) →
              s →∞ t₁ → s →∞ t₂ → t₁ ~ t₂
-}

ProperlyRefining : ∀{V} → T V → Pred (Subst V V) _
ProperlyRefining t σ = ∀ v → v ∈ fv t → isCons (σ v)

record ProperlyRefiningSeq {V : Set} (t : T V) : Set where
  coinductive
  field
    hd-ref : Subst V V
    hd-is-ref : hd-ref ∈ ProperlyRefining t
    tl-ref : ProperlyRefiningSeq (app hd-ref t)
open ProperlyRefiningSeq public

{-

refining-on-subterms : ∀{V f α} (t : T V) → t ≡ sup (inj₁ (f , α)) →
                       ProperlyRefiningSeq t →
                       (i : ar Σ f) → ProperlyRefiningSeq (α i)
hd-ref    (refining-on-subterms ._ refl p i) = hd-ref p
hd-is-ref (refining-on-subterms ._ refl p i) = {!!}
tl-ref    (refining-on-subterms ._ refl p i) = {!!} -- refining-on-subterms {!!} {!!} {!!} {!!}

-- | A non-trivial substitution is a substitution σ, such that, for all v ∈ V
-- we have that either σ(v) is a non-trivial term or if it is a variable w, then
-- w = v.
-- This allows us to stop substituting the first time we hit a variable.
NonTrivSubst : Set → Set
NonTrivSubst V = ⨿ (Subst V V) λ σ → (∀ v → isVar (σ v) → σ v ≡ η v)

term-seq-from-subst-seq : ∀{V} (t : T V) → ProperlyRefiningSeq t → Stream (T V)
hd (term-seq-from-subst-seq t Δ) = t
tl (term-seq-from-subst-seq t Δ) =
  term-seq-from-subst-seq (app (hd-ref Δ) t) (tl-ref Δ)

var-app-lem : ∀{V} → (σ : Subst V V) → ∀ v → app σ (η v) ≡ σ v
var-app-lem = {!!}

∞term-from-subst-seq : ∀{V} (t : T V) → ProperlyRefiningSeq t → T∞ V
out (∞term-from-subst-seq {V} (sup (inj₁ (f , α))) Δ) = inj₁ (f , β)
  where
    β : ar Σ f → T∞ V
    β i = ∞term-from-subst-seq
          (α i)
          (refining-on-subterms (sup (inj₁ (f , α))) refl Δ i)
out (∞term-from-subst-seq {V} (sup (inj₂ v)) Δ) = {!!}
--  with fv (sup (inj₂ v)) v | hd-ref Δ v | hd-is-ref Δ v refl
  where
    g : ∀{σ} → σ ∈ ProperlyRefining (sup (inj₂ v)) → ⟪ Σ ⟫ (T∞ V)
    g {σ} p with σ v | p v refl
    g p | sup (inj₁ (f , α)) | tt = f , β
      where
        β : ar Σ f → T∞ V
        β i = ∞term-from-subst-seq
              (α i)
              (refining-on-subterms (sup (inj₁ (f , α)))
                                    refl
                                    {!!}
                                    i)
    g p | sup (inj₂ w) | ()

-}

{-

out (∞term-from-subst-seq {V} (sup (inj₂ v)) Δ) | p | sup (inj₁ (f , α)) | tt =
  inj₁ (f , β {!refl!})
  where
    foo : hd-ref Δ v ≡ sup (inj₁ (f , α)) → app (hd-ref Δ) (sup (inj₂ v)) ≡ sup (inj₁ (f , α))
    foo p =
      begin
        app (hd-ref Δ) (sup (inj₂ v))
      ≡⟨ {!!} ⟩
        hd-ref Δ v
      ≡⟨ {!refl!} ⟩
        sup (inj₁ (f , α))
      ∎

    β : hd-ref Δ v ≡ sup (inj₁ (f , α)) → ar Σ f → T∞ V
    β p i = ∞term-from-subst-seq
            (α i)
            (refining-on-subterms (sup (inj₁ (f , α)))
                                  refl
                                  (subst ProperlyRefiningSeq {!!} (tl-ref Δ))
                                  i)
          -- (app (hd-ref Δ) (η v)) (var-app-lem {!!} v)
out (∞term-from-subst-seq (sup (inj₂ v)) Δ) | p | sup (inj₂ y) | ()
-}

{-
∞term-from-subst-seq : ∀{V} → Stream (NonTrivSubst V) → T V → T∞ V
out (∞term-from-subst-seq Δ (sup (inj₁ (s , α)))) =
  inj₁ (s , (λ i → ∞term-from-subst-seq Δ (α i)))
out (∞term-from-subst-seq Δ (sup (inj₂ v))) with proj₁ (hd Δ) v | proj₂ (hd Δ) v
... | sup (inj₁ (s , α)) | f =
  inj₁ (s , (λ i → ∞term-from-subst-seq (tl Δ) (α i)))
... | sup (inj₂ v₁)      | f with f tt
out (∞term-from-subst-seq Δ (sup (inj₂ v))) | sup (inj₂ .v) | f | refl =
  inj₂ v
-}

{-
∞term-from-subst-seq-converges :
  ∀{V} → (Δ : Stream (NonTrivSubst V)) → (t : T V) →
  term-seq-from-subst-seq Δ t →∞ ∞term-from-subst-seq Δ t
-}
