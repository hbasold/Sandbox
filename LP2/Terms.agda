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

-- | T is free over Σ with inclusion
ι : ⟪ Σ ⟫ ⇒ T
ι = sup ∘ inj₁ ∘ ⟪ Σ ⟫₁ η

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

unifies : ∀{V W} → T V → T V → Subst V W → Set
unifies t s σ = app σ t ≡ app σ s

-- | Most general unifier
mgu : ∀{V W} → T V → T V → Subst V W → Set
mgu t s = least _⊑_ (unifies t s)

-- | Free variables
fv : ∀{V} → T V → Pred V _
fv (sup (inj₁ (s , α))) v = ⨿ (Sig.ar Σ s) λ i → (fv (α i) v)
fv (sup (inj₂ v₁))      v = v₁ ≡ v

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

{-
conv-branch : {V : Set} (R : Stream (T V) → T∞ V → Set) →
              Stream (T V) → T∞ V → Set
conv-branch R s t with hd s | out t
conv-branch R s t | sup (inj₁ (f , α)) | inj₁ (g , β) =
  ⨿ (f ≡ g) λ p →
  ⨿ (RootsMatch (tl s) f) λ q →
  ∀ i → R (split (tl s) f q i) (β (subst (ar Σ) p i))
conv-branch R s t | sup (inj₁ x) | inj₂ v       = ⊥
conv-branch R s t | sup (inj₂ v) | inj₁ (f , α) =
  ∃ λ n → first-root-match s f n × R (δ n s) t
conv-branch R s t | sup (inj₂ v) | inj₂ w       = v ≡ w × R (tl s) t
-}

-- | A sequence s of finite terms converges to a possibly infinite term,
-- if for all i, sᵢ₊₁ = sᵢ[σ] for some substitution σ : V → T V and t = sᵢ[τ]
-- for some τ : V → T∞ V.
-- Note that this coincides with convergence in the prefix metric.
record _→∞_ {V : Set} (s : Stream (T V)) (t : T∞ V) : Set where
  coinductive
  field
    conv-out : conv-branch _→∞_ s t (hd s) (out t)
{-
    hd-matches   : ∃ λ σ → hd (tl s) ≡ app σ (hd s)
    hd-prefix    : ∃ λ τ → t ~ app∞ τ (χ (hd s))
    tl-converges : tl s →∞ t
-}

open _→∞_ public

{-
lem₂ : ∀{V n f} {s : Stream (T V)} →
       first-root-match s f (suc n) → first-root-match (tl s) f n
lem₂ {n = n} {f} {s} (p , q) = (p , λ m → ≤-pred (q m))
-}

{-
lem₃ : ∀{V f} (s : Stream (T V)) → ∀{t} →
      first-root-match s f zero → s →∞ t → first-root-match (tl s) f zero
lem₃ s {t} m          c with hd s      | out t  | conv-out c
lem₃ s     (refl , q) c | sup (inj₁ _) | inj₁ _ | refl , p , _
  = (hd-match p , (λ m → z≤n))
lem₃ s     (refl , q) c | sup (inj₁ _) | inj₂ v | ()
lem₃ s     (() ,   q) c | sup (inj₂ v) | u      | r
-}

lem₆ : ∀{V} (s : Stream (T V)) → ∀{t f} →
       root-matches (hd s) f → s →∞ t → RootsMatch (tl s) f
hd-match (lem₆ s {t} m    c) with hd s | out t | conv-out c
hd-match (lem₆ s     refl c) | sup (inj₁ (f , α)) | inj₁ (.f , β) | refl , m₁ , br = hd-match m₁
hd-match (lem₆ s     refl c) | sup (inj₁ (f , α)) | inj₂ y | ()
hd-match (lem₆ s     ()   c) | sup (inj₂ v) | x | y
tl-match (lem₆ s {t} m    c) with hd s | out t | conv-out c
tl-match (lem₆ s     refl c) | sup (inj₁ (f , α)) | inj₁ (.f , β) | refl , m₁ , br = tl-match m₁
tl-match (lem₆ s     refl c) | sup (inj₁ (f , α)) | inj₂ y | ()
tl-match (lem₆ s     ()   c) | sup (inj₂ v) | x | y

lem₅ : ∀{V} (s : Stream (T V)) → ∀{t f} →
       root-matches (hd s) f → s →∞ t → tl s →∞ t
conv-out (lem₅ s {t} m    c) with hd s | out t | conv-out c
conv-out (lem₅ s     refl c) | sup (inj₁ (f , α)) | inj₁ (.f , β) | refl , m , br = {!!}
conv-out (lem₅ s     refl c) | sup (inj₁ (f , α)) | inj₂ y | ()
conv-out (lem₅ s     ()   c) | sup (inj₂ v) | x | y

lem₇ : ∀{V} (s : Stream (T V)) → ∀{t f α} →
       RootsMatch (tl s) f → s →∞ t → hd s ≡ sup (inj₁ (f , α)) →
       ∃ λ β → hd (tl s) ≡ sup (inj₁ (f , β))
lem₇ = {!!}

lem₄ : ∀{V} (s : Stream (T V)) → ∀{t} →
      s →∞ t → tl s →∞ t
lem₄ {V} s {t} p = q {s} {t} (hd s) (out t) refl refl (conv-out p)
  where
    q : ∀{s t} → (u : T V) → (x : ⟪ Σ ⟫ (T∞ V) ⊎ V) →
        hd s ≡ u → out t ≡ x → conv-branch _→∞_ s t u x → tl s →∞ t
    conv-out (q {s} {t} (sup (inj₁ (f , α))) (inj₁ (.f , β)) hs≡u ot≡x (refl , m , br))
      = subst₂ (λ u₁ u₂ → conv-branch _→∞_ (tl s) t u₁ u₂)
               (sym (proj₂ (lem₇ s m
                                 (record { conv-out =
                                   subst₂ (λ u₁ u₂ → conv-branch _→∞_ s t u₁ u₂)
                                 (sym hs≡u) (sym ot≡x) (refl , (m , br)) })
                                 hs≡u)
                    )
               )
               (sym ot≡x) (refl , tl-match m , (λ i → lem₅ (split (tl s) f m i) {!!} (br i)))
      -- conv-branch _→∞_ (tl s₁) t₁ (hd (tl s₁)) (out t₁)
      -- conv-branch _→∞_ (tl .s) .t (hd (tl .s)) (out .t)
    q (sup (inj₁ x)) (inj₂ y) hs≡u ot≡x ()
    q (sup (inj₂ y)) (inj₁ (g , β)) hs≡u ot≡x (s₁ , match-hd x , c) = lem₅ s₁ x c
    q (sup (inj₂ y)) (inj₁ (g , β)) hs≡u ot≡x (._ , match-tl m , c) = c
--    conv-out (q (sup (inj₂ y)) (inj₁ (g , β)) hs≡u ot≡x (zero , m , br)) = {!!}
--    conv-out (q {s} {t} (sup (inj₂ y)) (inj₁ x) hs≡u ot≡x (suc n , m , br)) = {!!}
--      q {s} {t} (hd (δ n s)) (inj₁ x) {!!} ot≡x {!!}
--      q (hd (tl s)) (inj₁ x) ? ot≡x br
      --q (hd (δ n s)) (out t) refl refl (conv-out br)
    q (sup (inj₂ y)) (inj₂ y₁) hs≡u ot≡x br = proj₂ br


{-
lem₄ : ∀{V} (s : Stream (T V)) → ∀{t} →
      s →∞ t → tl s →∞ t
lem₄ {V} s {t} p = q {s} {t} (hd s) (out t) refl refl (conv-out p)
  where
    q : ∀{s t} → (u : T V) → (x : ⟪ Σ ⟫ (T∞ V) ⊎ V) →
        hd s ≡ u → out t ≡ x → conv-branch _→∞_ s t u x → tl s →∞ t
    q (sup (inj₁ (f , α))) (inj₁ (.f , β)) hs≡u ot≡x (refl , m , br) = {!!}
    q (sup (inj₁ x)) (inj₂ y) hs≡u ot≡x ()
    conv-out (q (sup (inj₂ y)) (inj₁ (g , β)) hs≡u ot≡x (zero , m , br)) = {!!}
    conv-out (q {s} {t} (sup (inj₂ y)) (inj₁ x) hs≡u ot≡x (suc n , m , br)) = {!!}
--      q {s} {t} (hd (δ n s)) (inj₁ x) {!!} ot≡x {!!}
--      q (hd (tl s)) (inj₁ x) ? ot≡x br
      --q (hd (δ n s)) (out t) refl refl (conv-out br)
    q (sup (inj₂ y)) (inj₂ y₁) hs≡u ot≡x br = proj₂ br
-}
{-
lem₄ {V} s {t} p | sup (inj₁ (f , α)) | inj₁ (.f , β) | refl , m , r =
  q {!!} m r
  where
     q : {s' : Stream (T V)} {t : T∞ V} {f : ∥ Σ ∥} {β : ar Σ f → T∞ V} →
         out t ≡ inj₁ (f , β) →
         (m : RootsMatch s' f) →
         ((i : ar Σ f) → split s' f m i →∞ β i) →
         s' →∞ t
     conv-out (q {s'} {t} ts m n) with hd s' | hd-match m | out t
     conv-out (q {s'} refl m n) | sup (inj₁ (f₁ , α₁)) | refl | inj₁ (.f₁ , β₁)
       = (refl , tl-match m , (λ i → lem₄ (split s' f₁ m i) (n i)))
     conv-out (q () m₁ n) | sup (inj₁ (f₁ , α₁)) | refl | inj₂ v
     conv-out (q ts m n) | sup (inj₂ y) | () | u
lem₄ s p | sup (inj₁ x) | inj₂ y | ()
lem₄ s p | sup (inj₂ y) | inj₁ x | r = {!!}
lem₄ s p | sup (inj₂ y) | inj₂ y₁ | r = proj₂ r
-}

{-
lem₁ : ∀{V} (n k : ℕ) (s : Stream (T V)) → ∀{f g t} →
      first-root-match s f n → first-root-match s g k →
      δ n s →∞ t → δ k s →∞ t → f ≡ g
lem₁ n k s {f} {g} {t} m₁ m₂ c₁ c₂
  with s at n | s at k | m₁ | m₂
       | out t | conv-out c₁ | conv-out c₂
lem₁ zero zero s _ _ c₁ c₂
  | sup (inj₁ (f , α)) | sup (inj₁ (g , β)) | (refl , p) | (refl , q)
  | inj₁ x | w | r =
    trans (proj₁ w) (sym (proj₁ r))
lem₁ zero zero s _ _ c₁ c₂
  | sup (inj₁ (f , α)) | sup (inj₁ (g , β)) | (refl , p) | (refl , q)
  | inj₂ y | () | r
lem₁ zero zero s _ _ c₁ c₂
  | sup (inj₁ (f , α)) | sup (inj₂ y) | (refl , p) | (() , q)
  | v | w | r
lem₁ zero zero s _ _ c₁ c₂
  | sup (inj₂ y) | u | (() , p) | m₂
  | v | w | r
lem₁ zero (suc k) s m₁ m₂ c₁ c₂ | u | u₁ | m₁' | m₂'
  | v | w | r = lem₁ zero k (tl s) (lem₃ s m₁ c₁) {!m₂!} (lem₄ s c₁) c₂
lem₁ (suc n) zero s _ _ c₁ c₂ | u | u₁ | m₁ | m₂ | v | w | r = {!!}
lem₁ (suc n) (suc k) s m₁ m₂ c₁ c₂
  | u | u₁ | _ | _
  | v | w | r = lem₁ n k (tl s) (lem₂ m₁) (lem₂ m₂) c₁ c₂

lem : ∀{V} (n k : ℕ) {s : Stream (T V)} → ∀{f g t} →
      first-root-match s f n → first-root-match s g k →
      δ n s →∞ t → δ k s →∞ t → n ≡ k
lem n k p q c₁ c₂ =
  least-unique NatTO n k p (subst _ (sym (lem₁ n k _ p q c₁ c₂)) q)
  where
    NatTO = TotalOrder.isTotalOrder (DecTotalOrder.totalOrder Nat.decTotalOrder)
{-
lem n k {s} {f} {g} {t} (m₁ , p) (m₂ , q) c₁ c₂ with conv-out c₁ | conv-out c₂
lem zero zero (m₁ , p) (m₂ , q) c₁ c₂ | u | v = refl
lem zero (suc k) (m₁ , p) (m₂ , q) c₁ c₂ | u | v = {!!}
lem (suc n) zero (m₁ , p) (m₂ , q) c₁ c₂ | u | v = {!!}
lem (suc n) (suc k) {s} (m₁ , p) (m₂ , q) c₁ c₂ | u | v =
  cong suc (lem n k {tl s} (m₁ , {!!}) {!!} {!!} {!!})
-}

unique-conv : ∀{V} (s : Stream (T V)) (t₁ t₂ : T∞ V) →
              s →∞ t₁ → s →∞ t₂ → t₁ ~ t₂
out~ (unique-conv s t₁ t₂ p q)
  with hd s | out t₁ | out t₂ | conv-out p | conv-out q
out~ (unique-conv s t₁ t₂ p q)
  | sup (inj₁ (._ , α)) | inj₁ (._ , β) | inj₁ (f , γ)
  | refl , q₁ , ω₁ | refl , q₂ , ω₂
  = refl
    , (λ {i} → unique-conv (split (tl s) f q₁ i)
                           (β i)
                           (γ i)
                           (ω₁ i)
                           (subst (λ u → split (tl s) f u i →∞ γ i)
                                  (RootsMatch-unique q₂ q₁)
                                  (ω₂ i)))
out~ (unique-conv s t₁ t₂ p q)
  | sup (inj₁ x) | inj₁ x₁ | inj₂ y | y₁ | ()
out~ (unique-conv s t₁ t₂ p q)
  | sup (inj₁ x) | inj₂ y | x₁ | () | z
out~ (unique-conv s t₁ t₂ p q)
  | sup (inj₂ v) | inj₁ (f , α) | inj₁ (g , β) | (n , mg , p₁) | (k , mf , q₁)
  with s at n | s at k
out~ (unique-conv s t₁ t₂ p q)
  | sup (inj₂ v) | inj₁ (f , α) | inj₁ (.g , β) | n , m₁ , p₁ | k , (refl , r₂) , q₁
  | sup (inj₁ (f' , γ)) | sup (inj₁ (g , ρ)) =
  (lem₁ n k s ({!m₁!} , {!!}) {!!} {!!} {!!}) , {!!}
out~ (unique-conv s t₁ t₂ p q)
  | sup (inj₂ v) | inj₁ (f , α) | inj₁ (g , β) | n , mg , p₁ | k , (() , _) , q₁
  | sup (inj₁ x) | sup (inj₂ y)
out~ (unique-conv s t₁ t₂ p q)
  | sup (inj₂ v) | inj₁ (f , α) | inj₁ (g , β) | n , (() , _) , p₁ | k , mf , q₁
  | sup (inj₂ y) | b
out~ (unique-conv s t₁ t₂ p q) | sup (inj₂ y) | inj₁ x | inj₂ y₁ | y₂ | z = {!!}
out~ (unique-conv s t₁ t₂ p q) | sup (inj₂ y) | inj₂ y₁ | x₁ | y₂ | z = {!!}
-}

-- | A non-trivial substitution is a substitution σ, such that, for all v ∈ V
-- we have that either σ(v) is a non-trivial term or if it is a variable w, then
-- w = v.
-- This allows us to stop substituting the first time we hit a variable.
NonTrivSubst : Set → Set
NonTrivSubst V = ⨿ (Subst V V) λ σ → (∀ v → isVar (σ v) → σ v ≡ η v)

term-seq-from-subst-seq : ∀{V} → Stream (NonTrivSubst V) → T V → Stream (T V)
hd (term-seq-from-subst-seq Δ t) = t
tl (term-seq-from-subst-seq Δ t) = term-seq-from-subst-seq (tl Δ) (app (proj₁ (hd Δ)) t)

∞term-from-subst-seq : ∀{V} → Stream (NonTrivSubst V) → T V → T∞ V
out (∞term-from-subst-seq Δ (sup (inj₁ (s , α)))) =
  inj₁ (s , (λ i → ∞term-from-subst-seq Δ (α i)))
out (∞term-from-subst-seq Δ (sup (inj₂ v))) with proj₁ (hd Δ) v | proj₂ (hd Δ) v
... | sup (inj₁ (s , α)) | f =
  inj₁ (s , (λ i → ∞term-from-subst-seq (tl Δ) (α i)))
... | sup (inj₂ v₁)      | f with f tt
out (∞term-from-subst-seq Δ (sup (inj₂ v))) | sup (inj₂ .v) | f | refl =
  inj₂ v

{-
∞term-from-subst-seq-converges :
  ∀{V} → (Δ : Stream (NonTrivSubst V)) → (t : T V) →
  term-seq-from-subst-seq Δ t →∞ ∞term-from-subst-seq Δ t
hd-matches   (∞term-from-subst-seq-converges Δ t) = (proj₁ (hd Δ) , refl)
hd-prefix    (∞term-from-subst-seq-converges Δ t) = {!!}
tl-converges (∞term-from-subst-seq-converges Δ t) = {!∞term-from-subst-seq-converges!}
-}
