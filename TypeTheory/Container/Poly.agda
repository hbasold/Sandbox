{-# OPTIONS --copatterns --sized-types --without-K #-}
module Poly where

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

infixr 2 _and_

Fam : Set → Set₁
Fam I = I → Set

Fam₂ : Set → Set → Set₁
Fam₂ I J = I → J → Set

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

_and_ = _×_

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

-- | Turn morphism into a family
toFam : ∀ {A B : Set} → (h : B → A) → Fam A
toFam {A} {B} h a = Σ[ b ∈ B ] (h b ≡ a)

-- | Turn family into a morphism
fromFam : ∀ {A B : Set} → (X : Fam A) → (Σ A X → A)
fromFam {A} {B} X = proj₁

-- | Set comprehension
record ⟪_⟫' {A : Set} (φ : A → Set) : Set where
  constructor elem
  field
    a : A
    .isElem : φ a

inc : {A : Set} {φ : A → Set} → ⟪ φ ⟫' → A
inc (elem a isElem) = a

compr-syntax : (A : Set) (φ : A → Set) → Set
compr-syntax A = ⟪_⟫'

syntax compr-syntax A (λ x → φ) = ⟪ x ∈ A ∥ φ ⟫

compr-syntax' : {A : Set} (φ ψ : A → Set) → Set
compr-syntax' φ ψ = ⟪ (λ a → φ a and ψ a) ⟫'

syntax compr-syntax' φ (λ x → ψ) = ⟪ x ∈ φ ∥ ψ ⟫'

-- | Subsets of A
Sub : Set → Set₁
Sub A = Σ[ φ ∈ (A → Set) ] ⟪ φ ⟫'

_∈_ : {A : Set} → A → (φ : A → Set) → Set
x ∈ φ = φ x

_⊆_ : {A : Set} → (φ₁ φ₂ : A → Set) → Set
φ₁ ⊆ φ₂ = φ₁ ⇒ φ₂

_≅_ : {A : Set} → (φ₁ φ₂ : A → Set) → Set
φ₁ ≅ φ₂ = (φ₁ ⊆ φ₂) × (φ₂ ⊆ φ₁)

predToFam : {I A : Set} → (A → I) → (A → Set) → Fam I
predToFam {I} {A} h φ = Σ' h φ

-- | Dependent polynomials
record DPoly
  {I : Set} -- ^ Global index of constructed type
--  {N : Set}      -- ^ Index set for parameters
--  {J : N → Set}  -- ^ Index of each parameter
  {J : Set}
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
T : {I : Set} {J : Set} →
    DPoly {I} {J} →
    (X : Fam J) →  -- ^ Parameter
    (Fam I)
T {I} {N} (dpoly A s E p t) X =
  Σ' s     (λ a →
  Π' p (λ e →
    X (t e)
  ) a )

-- | Functorial action of T
T₁ : {I : Set} {J : Set} →
     (C : DPoly {I} {J}) →
     {X Y : J → Set} →
     (f : (j : J) → X j → Y j)
     (i : I) → T C X i → T C Y i
T₁ {I} {J} (dpoly A s E p t) {X} {Y} f .(s a) (ins a v) =
  ins a (Π'₁ ((t *₁) f) a v)

-- | Dependent, multivariate polynomials
record DMPoly
  {I : Set} -- ^ Global index of constructed type
  {N : Set}      -- ^ Index set for parameters
  {J : N → Set}  -- ^ Index of each parameter
  : Set₁ where
  constructor dpoly₁
  field
    -- J ←t- E -p→ A -s→ I
    A₁ : Set  -- ^ Labels
    s₁ : A₁ → I
    E₁ : N → Set
    p₁ : (n : N) → E₁ n → A₁
    t₁ : (n : N) → E₁ n → J n


-- | Create multiparameter polynomial
paramPoly : {I : Set} {N : Set} {J : N → Set} →
            DMPoly {I} {N} {J} →
            DPoly {I} {Σ N J}
paramPoly {I} {N} (dpoly₁ A₁ s₁ E₁ p₁ t₁) =
  dpoly
    A₁
    s₁
    ⟪ E₁ ⟫
    (λ {(n , e) → p₁ n e})
    (λ {(n , e) → (n , t₁ n e)})

-- | Functor on product category for multivariate polynomials.
TM : {I : Set} {N : Set} {J : N → Set} →
     DMPoly {I} {N} {J} →
     (X : (n : N) → J n → Set) →
     (I → Set)
TM P X = T (paramPoly P) (λ {(n , j) → X n j})


{-
----- Example: Vectors seen fixed point of (A, X) ↦ Σ z ⊤ + Σ s (A × X)
------   in the second variable. Here, z is the zero map, s the successor and
------   A is implicitely weakend.

Vec-Cons = Fin 2

Vec-Loc-Ind : Vec-Cons → Set
Vec-Loc-Ind zero    = ⊤
Vec-Loc-Ind (suc x) = ℕ

Vars : Set
Vars = Fin 2

Var-Types : Vars → Set
Var-Types zero    = ⊤
Var-Types (suc m) = ℕ

C : DPoly {ℕ} {Vars} {Var-Types}
C = dpoly ⟪ Vec-Loc-Ind ⟫ f Dom pp g
  where
    f : ⟪ Vec-Loc-Ind ⟫ → ℕ
    f (zero  , tt) = 0
    f (suc _ , k) = suc k

    -- | Domain exponents
    Dom' : Vars → Fam Vec-Cons
    Dom' _    zero = ⊥
    Dom' _    (suc _) = ℕ

    Dom : Vars → Set
    Dom zero = ⟪ Dom' zero ⟫
    Dom (suc n) = ⟪ Dom' (suc n) ⟫

    pp : (n : Vars) → Dom n → ⟪ Vec-Loc-Ind ⟫
    pp zero    (zero , ())
    pp (suc n) (zero , ())
    pp zero    (suc c , k) = suc c ⊢₁ k
    pp (suc n) (suc c , k) = suc c ⊢₁ k

    Params : Vars → ⟪ Vec-Loc-Ind ⟫ → Set
    Params x       (zero    , _) = ⊥
    Params zero    ((suc a) , k) = ⊤
    Params (suc x) ((suc a) , k) = ⊤

    g : (n : Vars) → Dom n → Var-Types n
    g zero    (zero , ())
    g (suc n) (zero , ())
    g zero    (suc c , k) = tt
    g (suc n) (suc c , k) = k

F : ((m : Vars) → Var-Types m → Set) → (ℕ → Set)
F = T C

-- Fix the variables, so that we can apply F.
Fix-Vars : Set → (ℕ → Set) → (p : Vars) → Var-Types p → Set
Fix-Vars A _ zero    _ = A
Fix-Vars A X (suc n)   = X

-- | Algebra structure on vectors, using the functor F.
in-vec : ∀ {A} → (n : ℕ) → F (Fix-Vars A (Vec A)) n → Vec A n
in-vec {A} .0       (ins (zero    , tt) _) = []
in-vec {A} .(suc k) (ins ((suc i) , k)  v) = a ∷ x
  where
    a : A
    a = app (suc i ⊢₁ k) (v zero)

    x : Vec A k
    x = app (suc i ⊢₁ k) (v (suc zero))

-- | Recursion for F-algebras
rec-vec : {A : Set} {X : ℕ → Set} →
          ((n : ℕ) → F (Fix-Vars A X) n → X n) →
          (n : ℕ) → Vec A n → X n
rec-vec {A} {X} u .0 [] = u 0 (ins (zero ⊢₁ tt) v₀)
  where
    v₀ : Π Vars (λ n → Π' (p C n) (λ e → Fix-Vars A X n (t C n e)) (zero ⊢₁ tt))
    v₀ zero = abs'' (zero ⊢₁ tt) q₀
      where
        q₀ : (i : E C zero) → p C zero i ≡ zero ⊢₁ tt → A
        q₀ (zero  , ()) p
        q₀ (suc d , _) ()
    v₀ (suc n) = abs'' (zero ⊢₁ tt) q₁
      where
        q₁ : (d : E C (suc n)) → p C (suc n) d ≡ zero ⊢₁ tt → X (t C (suc n) d)
        q₁ (zero  , ()) p
        q₁ (suc d , _) ()

rec-vec {A} {X} f (suc k) (a ∷ x) = f (suc k) (ins (suc zero ⊢₁ k) v')
  where
    v' : Π Vars     (λ n →
         Π' (p C n) (λ e →
         Fix-Vars A X n (t C n e)) (suc zero ⊢₁ k))
    v' zero = abs'' (suc zero ⊢₁ k) q₀
      where
        q₀ : (d : E C zero) → p C zero d ≡ suc zero ⊢₁ k → A
        q₀ d p = a
    v' (suc n) = abs'' (suc zero ⊢₁ k) q₁
      where
        q₁ : (d : E C (suc n)) →
             p C (suc n) d ≡ suc zero ⊢₁ k → X (t C (suc n) d)
        q₁ (zero  , ()) p
        q₁ (suc .zero , .k) refl = rec-vec f k x


--- Example 2: Partial streams

record ℕ∞ : Set where
  coinductive
  field
    pred∞ : ⊤ ⊎ ℕ∞
open ℕ∞

suc∞ : ℕ∞ → ℕ∞
pred∞ (suc∞ n) = inj₂ n

PS-Vars : Set
PS-Vars = Fin 2

PS-Types : PS-Vars → Set
PS-Types zero = ⊤
PS-Types (suc n) = ℕ∞

PS-C : DPoly {ℕ∞} {PS-Vars} {PS-Types}
PS-C = dpoly ℕ∞ id Codom codom-dep var-reidx
  where
    Codom : PS-Vars → Set
    Codom _ = ℕ∞

    codom-dep : (n : PS-Vars) → Codom n → ℕ∞
    codom-dep _ = suc∞

    var-reidx : (n : PS-Vars) → Codom n → PS-Types n
    var-reidx zero _ = tt
    var-reidx (suc v) = id

PS-F : ((m : PS-Vars) → PS-Types m → Set) → (ℕ∞ → Set)
PS-F = T PS-C

-- Fix the variables, so that we can apply F.
PS-Fix-Vars : Set → Fam ℕ∞ → (p : PS-Vars) → Fam (PS-Types p)
PS-Fix-Vars A _ zero    _ = A
PS-Fix-Vars A X (suc n)   = X

record PStr {i : Size} (A : Set) (n : ℕ∞) : Set where
  coinductive
  field
    out : ∀ {j : Size< i} → PS-F (PS-Fix-Vars A (PStr {j} A)) n
open PStr

P-hd : ∀ {A} {n : ℕ∞} → PStr A (suc∞ n) → A
P-hd {A} {n} s = q (out s)
  where
    q : PS-F (PS-Fix-Vars A (PStr A)) (suc∞ n) → A
    q (ins .(suc∞ n) v) = app n (v zero)

P-tl : ∀ {A} {n : ℕ∞} → PStr A (suc∞ n) → PStr A n
P-tl {A} {n} s = q (out s)
  where
    q : PS-F (PS-Fix-Vars A (PStr A)) (suc∞ n) → PStr A n
    q (ins .(suc∞ n) v) = app n (v (suc zero))

P-corec : {A : Set} {X : Fam ℕ∞} →
          (c : X ⇒ PS-F (PS-Fix-Vars A X)) →
          (∀{i} → X ⇒ PStr {i} A)
out (P-corec {A} {X} c n x) {j} = ins n (h n x)
  where
    h : (n : ℕ∞) → X n →
        Π PS-Vars     (λ v →
        Π' (p PS-C v) (λ e →
        PS-Fix-Vars A (PStr {j} A) v (t PS-C v e)) n)
    h n x zero  = abs'' n (q n x)
      where
        q : (n : ℕ∞) → (X n) → (d : E PS-C zero) → p PS-C zero d ≡ n → A
        q .(suc∞ n) x n refl = r (c (suc∞ n) x)
          where
            r : PS-F (PS-Fix-Vars A X) (suc∞ n) → A
            r (ins .(suc∞ n) ch) = app n (ch zero)

    h n x (suc v) = abs'' n (q n x)
      where
        q : (n : ℕ∞) → (X n) →
            (i : E PS-C (suc v)) →
            p PS-C (suc v) i ≡ n →
            PStr {j} A (t PS-C (suc v) i)
        q .(suc∞ k) x k refl = P-corec c k (r (c (suc∞ k) x))
          where
            r : PS-F (PS-Fix-Vars A X) (suc∞ k) → X k
            r (ins .(suc∞ k) ch) = app k (ch (suc zero))

------- End examples --------

-}

-- | Non-dependent polynomials in one variable
record Poly : Set₁ where
  constructor poly
  field
    Sym : Set
    Arit : Set
    f : Arit → Sym
open Poly

-- | Interpretation as functors
⟦_⟧ : Poly → Set → Set
⟦ poly A B f ⟧ X = Σ A ((Π' f) (λ e → X))

⟦_⟧₁ : {P : Poly} {A B : Set} → (A → B) → (⟦ P ⟧ A → ⟦ P ⟧ B)
⟦_⟧₁ {poly Sym Arit f} {A} {B} f₁ (a , v) = (a , abs'' a (v' a v))
  where
    v' : (a' : Sym) (v' : Π' f (λ e → A) a') (b : Arit) → f b ≡ a' → B
    v' ._ v' b refl = f₁ (app b v')

-- | Lifting to predicates
⟦_⟧' : (p : Poly) → ∀ {X} → Fam X → Fam (⟦ p ⟧ X)
⟦ poly A B f ⟧' P (s , α) = ∀ (x : toFam f s) → P (α x)

-- | Lifting to relations
⟦_⟧'' : (p : Poly) → ∀ {X Y} → Fam₂ X Y → Fam₂ (⟦ p ⟧ X) (⟦ p ⟧ Y)
⟦ poly A B f ⟧'' P (s₁ , α₁) (s₂ , α₂) =
  Σ[ e ∈ (s₁ ≡ s₂) ] (∀ (x : toFam f s₁) →
    P (α₁ x) (α₂ (proj₁ x , trans (proj₂ x) e)))

eq-preserving : ∀ {p X} (x y : ⟦ p ⟧ X) → x ≡ y → ⟦ p ⟧'' _≡_ x y
eq-preserving {p} x .x refl = refl , q
  where
    lem : ∀ {X : Set} {x y : X} (e : x ≡ y) → trans e refl ≡ e
    lem refl = refl

    q : (z : toFam (f p) (proj₁ x)) →
        proj₂ x z ≡ proj₂ x (proj₁ z , trans (proj₂ z) refl)
    q (s , e) = cong (λ u → proj₂ x (s , u)) (sym (lem e))

-- | Final coalgebras for non-dependent polynomials
record M {i : Size} (P : Poly) : Set where
  coinductive
  field
    ξ : ∀ {j : Size< i} → ⟦ P ⟧ (M {j} P)
open M

ξ'  : ∀ {P} → M P → ⟦ P ⟧ (M P)
ξ' x = ξ x

mutual
  -- | Equality for M types is given by bisimilarity
  record _~_ {P : Poly} (x y : M P) : Set where
    coinductive
    field
      ~pr : ⟦ P ⟧'' _~_ (ξ' x) (ξ' y)
open _~_ public

IsBisim : ∀{p X Y} → (X → ⟦ p ⟧ X) → (Y → ⟦ p ⟧ Y) → Fam₂ X Y → Set
IsBisim {p} f g _R_ = ∀ x y → x R y → ⟦ p ⟧'' _R_ (f x) (g y)

root : ∀ {P} → M P → Sym P
root = proj₁ ∘ ξ'

corec-M : ∀ {P : Poly} {X : Set} → (X → ⟦ P ⟧ X) → (∀{i} → X → M {i} P)
ξ (corec-M {poly Sym Arit f} {X} c x) {j} = (c₁ , abs'' c₁ (v x))
  where
    c₁ = proj₁ (c x)

    v : (x : X) (b : Arit) → f b ≡ proj₁ (c x) → M {j} (poly Sym Arit f)
    v x b p = corec-M c (proj₂ (c x) (b , p))

Bisim→~ : ∀{p X Y} {f : X → ⟦ p ⟧ X} {g : Y → ⟦ p ⟧ Y} {_R_} →
          IsBisim f g _R_ → ∀ x y → x R y → corec-M f x ~ corec-M g y
~pr (Bisim→~ isBisim x y xRy) with isBisim x y xRy
~pr (Bisim→~ {p} {X} {Y} {f} {g} isBisim x y xRy) | (e , β) =
  (e , (λ z →
    Bisim→~ isBisim
            (proj₂ (f x) z)
            (proj₂ (g y) (proj₁ z , trans (proj₂ z) e))
            (β z)))

{-
corec-M-hom : {P : Poly} {X : Set}
              (c : X → ⟦ P ⟧ X) →
              (x : X) → ξ' (corec-M c x) R~ ⟦ corec-M c ⟧₁ (c x)
sym≡  (corec-M-hom c x) = refl
arit~ (corec-M-hom {poly A B f} {X} c x) =
  abs₃ (proj₁ (c x)) {!!} -- (pr x (c x) refl refl)
  where
    P = poly A B f

    pr : (x : X)
         (x' : ⟦ P ⟧ X)
         (p₀ : x' ≡ c x)
         (p : proj₁ (ξ' (corec-M c x)) ≡ proj₁ (⟦ corec-M c ⟧₁ x'))
         (b : B)
         (p₁ : f b ≡ proj₁ (ξ' (corec-M c x))) →
--         (p₁ : f b ≡ proj₁ x') →
         arit~-pr (ξ' (corec-M c x)) (⟦ corec-M c ⟧₁ x') p (b , p₁)
    pr x₁ (._ , ._) refl p₁ b p₂ = {!!}
-}

record PolyHom (P₁ P₂ : Poly) : Set where
  constructor polyHom
  field
    SymMor : Sym P₁ → Sym P₂
    AritMor : (SymMor *) (toFam (f P₂)) ⇒ toFam (f P₁)

coalg : {P₁ P₂ : Poly} →
        PolyHom P₁ P₂ →
        (∀ X → ⟦ P₁ ⟧ X → ⟦ P₂ ⟧ X)
coalg {poly Sym₁ Arit₁ f₁} {poly Sym₂ Arit₂ f₂} (polyHom α β) X (a , v)
  = (α a , abs'' (α a) (v' a v))
    where
      v' : (a : Sym₁) (v :  Π' f₁ (λ e → X) a) (b : Arit₂) → f₂ b ≡ α a → X
      v' a v b p = v (β a (b , p))

-- | Functoriality
M₁ : ∀ {P₁ P₂} → PolyHom P₁ P₂ → M P₁ → M P₂
M₁ {P₁} h = corec-M (coalg h (M P₁) ∘ ξ')

-- | Product of maps
_⊗_ : {A B C D : Set} → (A → B) → (C → D) → (A × C → B × D)
(f ⊗ g) x = ((f (proj₁ x)) , (g (proj₂ x)))

⊗-eq : {A B C : Set} {f : A → C} {g : B → C}
       (a : A) (b : B) (p : f a ≡ g b)→
       (f ⊗ g) (a , b) ≡ (g b , g b)
⊗-eq {f = f} {g} a b p = ×-eq (f a) (g b) (g b) (g b) p refl

-- | Extend polynomial by index
I-poly : Poly → Set → Poly
I-poly P I = poly (Sym P × I) (Arit P × I) (f P ⊗ id)

_⋊_ = I-poly

{-
-- | Projects away the I from M (P × I)
u₁ : ∀ {i} → (P : Poly) (I : Set) → M (I-poly I P) → M {i} P
ξ (u₁ P I x) {j} = q (ξ x)
  where
    q : R (I-poly I P) (M (I-poly I P)) → ⟦ P ⟧ (M {j} P)
    q (s , v) = (proj₁ s , abs'' (proj₁ s) (r (s , v)))
      where
        r : (u : R (I-poly I P) (M (I-poly I P))) (a : Arit P) →
            f P a ≡ proj₁ (proj₁ u) → M {j} P
        r ((.(f P a) , i) , v) a refl = u₁ P I (app (a , i) v)
-}

-- | Forget changes of dependencies of a polynomial in one variable.
simple : {I : Set} → DPoly {I} {I} → Poly
simple C = poly (DPoly.A C) (DPoly.E C) (DPoly.p C)

↓_ = simple

module MTypes {I : Set} (C : DPoly {I} {I}) where
  open DPoly C
  P = ↓ C

  idx : M P → I
  idx = s ∘ root

  inj : (X : I → Set) → ⟪ T C X ⟫ → ⟦ ↓ C ⟧ ⟪ X ⟫
  inj X (.(s a) , (ins a v)) = (a , abs'' a (u a v))
    where
      u : (a' : A)
          (v' : Π' p (λ e → X (t e)) a')
          (b : E) →
          f (↓ C) b ≡ a' →
          ⟪ X ⟫
      u ._ v' b refl = (t b , app b v')

  -- | Applies r corecursively, thus essentially constructs an element of
  -- M (P × I) where the second component is given by r.
  u₁ : M P → M (P ⋊ I)
  u₁ = M₁ (polyHom α β)
    where
      α : Sym (↓ C) → Sym ((↓ C) ⋊ I)
      α = < id , s >

      β : (α *) (toFam (f P ⊗ id)) ⇒ toFam p
      β ._ ((b , ._) , refl) = (b , refl)

  K : ⟦ P ⋊ I ⟧ (M (P ⋊ I)) → ⟦ P ⋊ I ⟧ (M (P ⋊ I) × E)
  K (a , v) = (a , abs'' a (v' a v))
    where
      v' : (a : Sym (P ⋊ I))
           (v : Π' (f (P ⋊ I)) (λ e → M (P ⋊ I)) a)
           (bi : Arit (P ⋊ I)) →
           f (P ⋊ I) bi ≡ a →
           M (P ⋊ I) × E
      v' ._ v₁ bi refl = (v₁ (bi , refl) , proj₁ bi)

  φ : M (P ⋊ I) × Arit P → M (P ⋊ I)
  φ = corec-M c
    where
      h : ⟦ P ⋊ I ⟧ (M (P ⋊ I)) × Arit P → ⟦ P ⋊ I ⟧ (M (P ⋊ I) × Arit P)
      h (((a , i) , v) , b) =
        ((a , t b) ,
          abs'' (a , t b) (v' (a , t b) b v))
        where
          v' : (ai' : Sym (P ⋊ I))
               (b : Arit P)
               (v :  Π' (f (P ⋊ I)) (λ _ →
                     M (P ⋊ I)) (proj₁ ai' , i))
               (i : Arit (P ⋊ I)) →
               f (P ⋊ I) i ≡ ai' →
               M (P ⋊ I) × Arit P
          v' ._ b v₁ (b₁ , _) refl = (app (b₁ , i) v₁ , b)

      c :  M (P ⋊ I) × Arit P →
           ⟦ P ⋊ I ⟧ (M (P ⋊ I) × Arit P)
      c = h ∘ (ξ' ⊗ id)

  ψ : M (P ⋊ I) → M (P ⋊ I)
  ψ = corec-M c
    where
      c : M (P ⋊ I) → ⟦ P ⋊ I ⟧ (M (P ⋊ I))
      c = ⟦ φ ⟧₁ ∘ K ∘ ξ'

  u₂ : M P → M (P ⋊ I)
  u₂ = ψ ∘ u₁

{-
{-
-- | Same as u₂???
u₂' : ∀ {I} (C : DPoly {I}) →
      M (↓ C) → M (↓ C ⋊ I)
u₂' {I} C x = M₁ (polyHom α β) x
  where
    α : Sym (↓ C) → Sym ((↓ C) ⋊ I)
    α a = (a , t C {!!}) -- (root x)) -- (s C (root x)))

    β : (α *) (toFam (f (↓ C) ⊗ id)) ⇒ toFam (p C tt)
    β ._ ((a , ._) , refl) = (a , refl)

φ : {I : Set} (C : DPoly {I}) {i : Size} →
    M {i} (↓ C ⋊ I) × Arit (↓ C) → M {i} (↓ C ⋊ I)
ξ (φ {I} C (x , b)) {j} = q (ξ x)
  where
    m : ⟦ ↓ C ⋊ I ⟧ (M {j} (↓ C ⋊ I)) → Sym (↓ C ⋊ I)
    m ((a , i) , v) = (a , (t C b))

    q : ⟦ ↓ C ⋊ I ⟧ (M {j} (↓ C ⋊ I)) →
        ⟦ ↓ C ⋊ I ⟧ (M {j} (↓ C ⋊ I))
    q u = (m u , abs'' (m u) (v' u))
      where
        v' : (u : ⟦ ↓ C ⋊ I ⟧ (M {j} (↓ C ⋊ I)))
             (b : Arit (↓ C ⋊ I)) →
             f (↓ C ⋊ I) b ≡ m u →
             M {j} (↓ C ⋊ I)
        v' ((._ , i) , v) (b , ._) refl = φ C ((app (b , i) v) , b)

ψ : {I : Set} (C : DPoly {I}) {i : Size} →
    M {i} (↓ C ⋊ I) → M {i} (↓ C ⋊ I)
ξ (ψ {I} C x) {j} = q (ξ x)
  where
    q : ⟦ ↓ C ⋊ I ⟧ (M {j} (↓ C ⋊ I)) →
        ⟦ ↓ C ⋊ I ⟧ (M {j} (↓ C ⋊ I))
    q (a , v) = (a , abs'' a (v' (a , v)))
      where
        v' : (u' : ⟦ ↓ C ⋊ I ⟧ (M {j} (↓ C ⋊ I)))
             (a' : Arit (↓ C ⋊ I)) →
             f (↓ C ⋊ I) a' ≡ proj₁ u' →
             M {j} (↓ C ⋊ I)
        v' (._ , v) a' refl = φ C (app a' v , proj₁ a')

u₂ : ∀ {i} {I} (C : DPoly {I}) →
     M (↓ C) → M {i} (↓ C ⋊ I)
u₂ C = ψ C ∘ u₁ C
-}

  Vφ : (i : I) → (M P → Set)
  Vφ i x = (s (root x) ≡ i) × (u₁ x ≡ u₂ x)

--V' : {I : Set} (C : DPoly {I} {I}) → Fam I
--V' C = ⟪ Vφ C ⟫²

{-
lem₂ : {I : Set} {C : DPoly {I} {I}} →
       (x : M (↓ C))
       (b : E C)
       (v : Π' (p C) (λ e → M (↓ C)) (p C b)) →
       ξ' x ≡ (_ , v) →
       u₁ C x ≡ u₂ C x →
       u₁ C (app b v) ≡ u₂ C (app b v)
lem₂ {I} {C} x b v pr≡ u₁≡u₂ = {!!}
  where
    w : (x : ⟦ ↓ C ⟧ (M (↓ C)))
        (b : E C)
        (v : Π' (p C) (λ e → M (↓ C)) (p C b)) →
        x ≡ (_ , v) →
        u₁ C (app b v) ≡ u₂ C (app b v)
    w ._ b v refl = {!!}

--    bar : ξ' (u₁ C x) ≡ ⟦ ↓ C ⟧₁ u₁ (M₁ 

lem₁ : {I : Set} {C : DPoly {I} {I}} →
       (x : M (↓ C))
       (b : E C)
       (v : Π' (p C) (λ e → M (↓ C)) (p C b)) →
       ξ' x ≡ (_ , v) →
       u₁ C x ≡ u₂ C x →
       s C (root (app b v)) ≡ t C b
lem₁ x b v pr≡ u₁≡u₂ = {!!}

{-
ξV  : ∀ {I} {C : DPoly {I} {I}} →
      V' C ⇒ T C (V' C)
ξV {C = dpoly A s E p t} .(s (proj₁ (ξ x))) (x , refl , u₁≡u₂)
  = ins (root x) (abs'' (root x) (v' (root x) (proj₂ (ξ' x)) refl))
  where
    C = dpoly A s E p t

    v' : (a : A)
         (v : Π' p (λ e → M (↓ C)) a)
         (q : ξ' x ≡ (a , v))
         (b : E) →
         p b ≡ a →
         Σ (M (↓ C)) (Vφ C (t b))
    v' .(p b) v q b refl =
      (app b v
      , lem₁ x b v q u₁≡u₂
      , (lem₂ x b v q u₁≡u₂))
-}

-}

  V' : M P → Set
  V' x = u₁ x ≡ u₂ x

  Φ : (M P → Set) → (M P → Set)
  Φ U x =
    let (a , v) = ξ' x
    in Π'' (f P) a (λ {(b , pr) →
       Σ[ y ∈ M P ] (
         U y and
         idx y ≡ t b and
         q b (a , v) pr y ) })
    where
      q : (b : E) (u : ⟦ P ⟧ (M P)) → f P b ≡ proj₁ u → M P → Set
      q b (._ , v) refl y = app b v ≡ y

{-
      q : (b : E) (u : ⟦ P ⟧ (M P)) → f P b ≡ proj₁ u →
          (j : I) → U' j → Set
      q b (._ , v) refl .(idx y) (ins y z) = app b v ≡ y
-}

{-
  V'-postFP : V' ⊆ Φ V'
  V'-postFP x x∈V' (b , fb≡ξx₁) = (r b (ξ' x) fb≡ξx₁ , {!!})
    where
      r : (b₁ : E) (u : ⟦ P ⟧ (M P)) →
          f P b₁ ≡ proj₁ u →
          predToFam idx V' (t b₁)
      r b₁ (._ , v) refl = r' b₁ (app b₁ v)
        where
          r' : (b₂ : E) (x' : M P) → predToFam idx V' (t b₂)
          r' b₂ x' = ins ? {!!}
-}
  V'-final : (U : M P → Set) → U ⊆ Φ U → U ⊆ V'
  V'-final = {!!}

  -- | This predicate on M (↓ C) ensures that we can define a map
  -- V → s a ≡ ⟦ ↓ C ⟧ (i × (t *) V.
  record V-pred (i : I) (x : M P) : Set where
    coinductive
    field
      -- | For ξ x = (a , v), we require s a = i
      sigma-idx : s (proj₁ (ξ x)) ≡ i
      -- | For ξ x = (a , v), we require ∀ b with p b = a that
      -- idx (v b) = s a and v b ∈ V (t b)
      reidx : Π'' (f P) (proj₁ (ξ x))
              (λ {(e , eq) → idx ((proj₂ (ξ x)) (e , eq)) ≡ t e
                             × V-pred (t e) ((proj₂ (ξ x)) (e , eq)) })
  open V-pred

{-
V : {I : Set} (C : DPoly {I} {I}) → Fam I
V C i = Σ (M (↓ C)) (V-pred C i)

Σ≡₁ : {I : Set} {A : Fam I} → {x y : Σ I A} → x ≡ y → proj₁ x ≡ proj₁ y
Σ≡₁ {x = i , a} {.i , .a} refl = refl

foofoo : {I : Set} {A : Fam I} → (x y : Σ I A) →
         (p : x ≡ y) → A (proj₁ y)
foofoo x .x refl = proj₂ x

Σ≡₂ : {I : Set} {A : Fam I} → {x y : Σ I A} →
        (p : x ≡ y) → foofoo x y p ≡ proj₂ y
Σ≡₂ {x = i , a} {.i , .a} refl = refl

out-V : {I : Set} {C : DPoly {I} {I}} →
        V C ⇒ T C (V C)
out-V {I} {C = dpoly A s E p t} i (x , v-proof)
  = foo i v-proof (sigma-idx v-proof)
  where
    P : DPoly
    P = dpoly A s E p t

    u : ⟦ ↓ P ⟧ (M (↓ P))
    u = ξ x

--    uaie : (u' : ⟦ ↓ P ⟧ (M (↓ P))) → f (↓ P) e ≡ proj₁ u' → A → Set
--    uaie u' pr = Π' (p tt) (λ e → V-pred P (t e) ((proj₂ u') (e , {!!})))

    foo : (i' : I) → V-pred P i' x → s (proj₁ u) ≡ i' → T P (V P) i'
    foo .(s (proj₁ u)) pr refl =
      ins (proj₁ u) (v'' u refl)
      where
        v'' : (u' : ⟦ ↓ P ⟧ (M (↓ P))) →
              u' ≡ ξ x →
              Π' p (λ e → V P (t e)) (proj₁ u')
        v'' (.(p e) , v) u'=ξx (e , refl) = (x' , {!!}) -- bar x {!v!} {!!} {!!} pr)
          where
            x' : M (↓ P)
            x' = v (e , refl)

            aiu = proj₂ (reidx pr (e , {!!}))

            bar : (x' : M (↓ P))
                  (v₁ : Π' (f (↓ P)) (λ e₁ → M (↓ P)) (proj₁ (ξ x'))) →
                  v₁ ≡ proj₂ (ξ x') →
                  (q : f (↓ P) e ≡ proj₁ (ξ x')) →
                  V-pred P (s (proj₁ (ξ x'))) x' → V-pred P (t e) (v₁ (e , q))
            bar x'' .(proj₂ (ξ x'')) refl q pr' = proj₂ (reidx pr' (e , q))

            tu : s (root (proj₂ (ξ x) (e , Σ≡₁ u'=ξx))) ≡ t e
            tu = proj₁ (reidx pr (e , Σ≡₁ u'=ξx))

{-
            bar : (v₁ : Π' (f (↓ P)) (λ e₁ → M (↓ P)) (proj₁ (ξ x))) →
                  v₁ ≡ proj₂ (ξ x) →
                  V-pred P (t e) x'
            bar ._ refl = proj₂ (reidx pr ?)
-}
            tiu : V-pred P (t e) (proj₂ (ξ x) (e , Σ≡₁ u'=ξx))
            tiu = proj₂ (reidx pr (e , Σ≡₁ u'=ξx))

-- Want out-s : M (↓ C ⋊ I) → T C (M {i} (↓ C ⋊ I))

T' : {I : Set} →
     DPoly {I} {I} →
     (X : I → Set) →  -- ^ Parameter
     (I → Set)
T' C X = T C {!!}

{-
out-s' : ∀ {i} {I} {C : DPoly {I}} →
         M (↓ C ⋊ I) → T' C (M {i} (↓ C ⋊ I))
out-s' = ?
-}

-- | Candidate for R C
out-s : ∀ {i} {I} {C : DPoly {I}} →
        M (↓ C ⋊ I) → ⟦ ↓ C ⟧ (M {i} (↓ C ⋊ I))
out-s {i} {I} {C} x = (q (ξ x) , abs'' (q (ξ x)) (h (ξ x)))
  where
    q : ⟦ ↓ C ⋊ I ⟧ (M {i} (↓ C ⋊ I)) → Sym (↓ C)
    q (a , _) = proj₁ a

    h : (u : ⟦ ↓ C ⋊ I ⟧ (M {i} (↓ C ⋊ I)))
        (a : Arit (↓ C)) →
        f (↓ C) a ≡ q u → M {i} (↓ C ⋊ I)
    h ((._ , b) , v') a refl = app (a , b) v'
-}
-}
