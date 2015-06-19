{-# OPTIONS --copatterns --sized-types #-}
module Poly where

open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Unit
open import Data.Empty
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Sum
open import Size

Fam : Set → Set₁
Fam I = I → Set

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

-- | Comprehension
⟦_⟧ : {I : Set} → Fam I → Set
⟦_⟧ {I} B = Σ I B

π : {I : Set} → (B : Fam I) → ⟦ B ⟧ → I
π B = proj₁

_⊢₁_ : {I : Set} {A : Fam I} → (i : I) → A i → ⟦ A ⟧
i ⊢₁ a = (i , a)

_,_⊢₂_ : {I : Set} {A : Fam I} {B : Fam ⟦ A ⟧} →
         (i : I) → (a : A i) → B (i , a) → ⟦ B ⟧
i , a ⊢₂ b = ((i , a) , b)

-- Not directly definable...
-- record Π' {A B : Set} (u : A → B) (P : A → Set) : B → Set where
--  field
--    app : (a : A) → Π' u P (u a) → P a

-- | ... but this does the job.
Π' : {I J : Set} (u : I → J) (P : Fam I) → Fam J
Π' {I} u P j = Π (Σ I (λ i → (u i ≡ j))) (λ { (i , _) → P i})

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

-- | Functorial action of Π'
Π'₁ : {I J : Set} {u : I → J} {P Q : Fam I} →
        (f : P ⇒ Q) → (Π' u P ⇒ Π' u Q)
Π'₁ {u = u} f .(u i) g (i , refl) = f i (app i g)

-- | Dependent polynomials
record DPoly
  {I : Set} -- ^ Global index of constructed type
  {N : Set}      -- ^ Index set for parameters
  {J : N → Set}  -- ^ Index of each parameter
  : Set₁ where
  constructor dpoly
  field
    A : Set  -- ^ Labels
    s : A → I
    E : N → Set
    p : (n : N) → E n → A
    t : (n : N) → E n → J n
open DPoly

-- | Interpretation of polynomial as functor
T : {I : Set} {N : Set} {J : N → Set} →
    DPoly {I} {N} {J} →
    (X : (n : N) → J n → Set) →  -- ^ Parameter
    (I → Set)
T {I} {N} (dpoly A s E p t) X =
  Σ' s     (λ a →
  Π N      (λ n →
  Π' (p n) (λ e →
    X n (t n e)
  ) a ))

-- | Functorial action of T
T₁ : {I : Set} {N : Set} {J : N → Set} →
     (C : DPoly {I} {N} {J}) →
     {X Y : (n : N) → J n → Set} →
     (f : (n : N) (j : J n) → X n j → Y n j)
     (i : I) → T C X i → T C Y i
T₁ {I} {N} {J} (dpoly A s E p t) {X} {Y} f .(s a) (ins a v) =
  ins a (λ n → Π'₁ (((t n) *₁) (f n)) a (v n))


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
C = dpoly ⟦ Vec-Loc-Ind ⟧ f Dom pp g
  where
    f : ⟦ Vec-Loc-Ind ⟧ → ℕ
    f (zero  , tt) = 0
    f (suc _ , k) = suc k

    -- | Domain exponents
    Dom' : Vars → Fam Vec-Cons
    Dom' _    zero = ⊥
    Dom' _    (suc _) = ℕ

    Dom : Vars → Set
    Dom zero = ⟦ Dom' zero ⟧
    Dom (suc n) = ⟦ Dom' (suc n) ⟧

    pp : (n : Vars) → Dom n → ⟦ Vec-Loc-Ind ⟧
    pp zero    (zero , ())
    pp (suc n) (zero , ())
    pp zero    (suc c , k) = suc c ⊢₁ k
    pp (suc n) (suc c , k) = suc c ⊢₁ k

    Params : Vars → ⟦ Vec-Loc-Ind ⟧ → Set
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

-- | Non-dependent polynomials in one variable
record Poly : Set₁ where
  constructor poly
  field
    Sym : Set
    Arit : Set
    f : Arit → Sym
open Poly

-- | Interpretation as functors
R : Poly → Set → Set
R (poly B E f) X = Σ B ((Π' f) (λ e → X))

-- | Final coalgebras for non-dependent polynomials
record M {i : Size} (P : Poly) : Set where
  coinductive
  field
    ξ : ∀ {j : Size< i} → R P (M {j} P)
open M

-- | Product of maps
_⊗_ : {A B C D : Set} → (A → B) → (C → D) → (A × C → B × D)
(f ⊗ g) x = ((f (proj₁ x)) , (g (proj₂ x)))

-- | Extend polynomial by index
I-poly : Poly → Set → Poly
I-poly P I = poly (Sym P × I) (Arit P × I) (f P ⊗ id)

_⋊_ = I-poly

{-
-- | Projects away the I from M (P × I)
u₁ : ∀ {i} → (P : Poly) (I : Set) → M (I-poly I P) → M {i} P
ξ (u₁ P I x) {j} = q (ξ x)
  where
    q : R (I-poly I P) (M (I-poly I P)) → R P (M {j} P)
    q (s , v) = (proj₁ s , abs'' (proj₁ s) (r (s , v)))
      where
        r : (u : R (I-poly I P) (M (I-poly I P))) (a : Arit P) →
            f P a ≡ proj₁ (proj₁ u) → M {j} P
        r ((.(f P a) , i) , v) a refl = u₁ P I (app (a , i) v)
-}

-- | Forget changes of dependencies of a polynomial in one variable.
simple : {I : Set} → DPoly {I} {⊤} {λ _ → I} → Poly
simple C = poly (A C) (E C tt) (p C tt)

↓_ = simple

-- | Applies r corecursively, thus essentially constructs an element of
-- M (P × I) where the second component is given by r.
u₁ : ∀ {i} {I} (C : DPoly {I}) →
   M {i} (↓ C) → M {i} (↓ C ⋊ I)
ξ (u₁ {i} {I} C x) {j} = q (ξ x)
  where
    ↓C = ↓ C
    r = s C

    q : R ↓C (M {j} ↓C) → R (↓C ⋊ I) (M {j} (↓C ⋊ I))
    q (a , v) = ((a , (r a)) , abs'' (a , (r a)) (v' (a , v)))
      where
        v' : (u : R ↓C (M {j} ↓C)) (i : Arit (↓C ⋊ I)) →
             f (↓C ⋊ I) i ≡ (proj₁ u , r (proj₁ u)) →
             M {j} (↓C ⋊ I)
        v' (._ , v) (i , ._) refl = u₁ C (app i v)

φ : {I : Set} (C : DPoly {I}) {i : Size} →
    M {i} (↓ C ⋊ I) × Arit (↓ C) → M {i} (↓ C ⋊ I)
ξ (φ {I} C (x , b)) {j} = q (ξ x)
  where
    m : R (↓ C ⋊ I) (M {j} (↓ C ⋊ I)) → Sym (↓ C ⋊ I)
    m ((a , i) , v) = (a , (t C tt b))

    q : R (↓ C ⋊ I) (M {j} (↓ C ⋊ I)) →
        R (↓ C ⋊ I) (M {j} (↓ C ⋊ I))
    q u = (m u , abs'' (m u) (v' u))
      where
        v' : (u : R (↓ C ⋊ I) (M {j} (↓ C ⋊ I)))
             (b : Arit (↓ C ⋊ I)) →
             f (↓ C ⋊ I) b ≡ m u →
             M {j} (↓ C ⋊ I)
        v' ((._ , i) , v) (b , ._) refl = φ C ((app (b , i) v) , b)

ψ : {I : Set} (C : DPoly {I}) {i : Size} →
    M {i} (↓ C ⋊ I) → M {i} (↓ C ⋊ I)
ξ (ψ {I} C x) {j} = q (ξ x)
  where
    q : R (↓ C ⋊ I) (M {j} (↓ C ⋊ I)) →
        R (↓ C ⋊ I) (M {j} (↓ C ⋊ I))
    q (a , v) = (a , abs'' a (v' (a , v)))
      where
        v' : (u' : R (↓ C ⋊ I) (M {j} (↓ C ⋊ I)))
             (a' : Arit (↓ C ⋊ I)) →
             f (↓ C ⋊ I) a' ≡ proj₁ u' →
             M {j} (↓ C ⋊ I)
        v' (._ , v) a' refl = φ C (app a' v , proj₁ a')

u₂ : ∀ {i} {I} (C : DPoly {I}) →
     M (↓ C) → M {i} (↓ C ⋊ I)
u₂ C = ψ C ∘ u₁ C


-- Want out-s : M (↓ C ⋊ I) → T C (M {i} (↓ C ⋊ I))

-- | Candidate for R C
out-s : ∀ {i} {I} {C : DPoly {I}} →
        M (↓ C ⋊ I) → R (↓ C) (M {i} (↓ C ⋊ I))
out-s {i} {I} {C} x = (q (ξ x) , abs'' (q (ξ x)) (h (ξ x)))
  where
    q : R (↓ C ⋊ I) (M {i} (↓ C ⋊ I)) → Sym (↓ C)
    q (a , _) = proj₁ a

    h : (u : R (↓ C ⋊ I) (M {i} (↓ C ⋊ I)))
        (a : Arit (↓ C)) →
        f (↓ C) a ≡ q u → M {i} (↓ C ⋊ I)
    h ((._ , b) , v') a refl = app (a , b) v'
