-- | In this module we show that the substream relation is transitive.

open import Size
open import Streams
open import Relation.Binary.PropositionalEquality as P
open import Data.Product
open import Function

tl' : ∀{A} → Stream A → Stream A
tl' s = tl s {∞}

{-
data Reachable {A : Set} (P : A → Set) : Stream A → Set where
  nowR : (s : Stream A) → P (hd s) → Reachable P s
  laterR : (s : Stream A) → Reachable P (tl s) → Reachable P (tl s)
-}

{-
data Eventually {A : Set} (P : A → Set) (s : Stream A) : Set where
  now : P (hd s) → Eventually P s
  later : Eventually P (tl s) → Eventually P s

-}

record Always {A : Set} (P : A → Set) (s : Stream A) : Set where
  coinductive
  field
    hd-valid : P (hd s)
    tl-valid : Always P (tl s)

open Always public

Always-coiter : ∀{A} {P : A → Set} {B : Stream A → Set}
                (hv : ∀ s → B s → P (hd s))
                (tv : ∀ s → B s → B (tl s)) →
                ∀ s → B s → Always P s
hd-valid (Always-coiter hv tv s b) = hv s b
tl-valid (Always-coiter hv tv s b) = Always-coiter hv tv (tl s) (tv s b)

data E {A : Set} (P : A → Set) (F : Stream A → Set) (s : Stream A) : Set where
  now : P (hd s) → F (tl s) → E P F s
  later : E P F (tl s) → E P F s

record Fair {A : Set} (P : A → Set) (s : Stream A) : Set where
  coinductive
  field
    step : E P (Fair P) s

open Fair public

Eventually : ∀{A} → (P : A → Set) → Stream A → Set
Eventually P = E P (Fair P)

Fair-coiter : ∀{A} {P : A → Set} {B : Stream A → Set}
              (st : ∀ s → B s → E P B s) →
              ∀ s → B s → Fair P s
xFair-coiter : ∀{A} {P : A → Set} {B : Stream A → Set}
               (st : ∀ s → B s → E P B s) →
               ∀ s → E P B s → Eventually P s

step (Fair-coiter st s b) = xFair-coiter st s (st s b)

xFair-coiter st s (now p b) = now p (Fair-coiter st (tl s) b)
xFair-coiter st s (later e) = later (xFair-coiter st (tl s) e)

Stream-coiter : ∀{A B : Set} → (B → A) → (B → B) → B → Stream A
hd (Stream-coiter h t b) = h b
tl (Stream-coiter h t b) = Stream-coiter h t (t b)

∃-elim : ∀{A : Set} {B : A → Set} {C : Set} →
         ((a : A) → B a → C) →
         Σ A B → C
∃-elim f (a , b) = f a b

≡-elim : ∀{A : Set} {B : A → A → Set} →
         ((x : A) → B x x) →
         {x y : A} → x ≡ y → B x y
≡-elim f {x = x} refl = f x

Always-coind : ∀{A} {P : A → Set} {B : Set} -- {C : Stream A → Set}
               {h : B → A} {t : B → B}
               (hv : ∀ b → P (h b))
               → ∀ b → Always P (Stream-coiter h t b)
Always-coind {A} {P = P} {B} {h} {t} hv b =
  Always-coiter {B = λ s → ∃ λ b → s ≡ Stream-coiter h t b}
                f g (Stream-coiter h t b) (b , refl)
  where
    f : (s : Stream A) → ∃ (λ b → s ≡ Stream-coiter h t b) → P (hd s)
    f s = ∃-elim u
      where
        u : (b : B) → s ≡ Stream-coiter h t b → P (hd s)
        u b p = subst P (sym (cong hd p)) (hv b)

    g : (s : Stream A) →
        ∃ (λ b → s ≡ Stream-coiter h t b) →
        ∃ (λ b → tl s ≡ Stream-coiter h t b)
    g s = ∃-elim u
      where
        u : (b : B) → s ≡ Stream-coiter h t b →
            ∃ (λ b₁ → tl s ≡ Stream-coiter h t b₁)
        u b p = (t b , cong tl' p)
{-
hd-valid (Always-coind h t hv b) = hv b
tl-valid (Always-coind h t hv b) = Always-coind h t hv (t b)
-}

dcoiter-Fair : ∀{A} {P : A → Set} {B : Set} {C : Stream A → Set}
  {h : B → A} {t : B → B}
  (st : ∀ b → C (Stream-coiter h t b) → E P C (Stream-coiter h t b)) →
  ∀ b → C (Stream-coiter h t b) → Fair P (Stream-coiter h t b)
xdcoiter-Fair : ∀{A} {P : A → Set} {B : Set} {C : Stream A → Set}
  {h : B → A} {t : B → B}
  (st : ∀ b → C (Stream-coiter h t b) → E P C (Stream-coiter h t b)) →
  ∀ b → E P C (Stream-coiter h t b) → Eventually P (Stream-coiter h t b)
step (dcoiter-Fair st b c) = xdcoiter-Fair st b (st b c)

xdcoiter-Fair st b (now p c) = now p (dcoiter-Fair st _ c)
xdcoiter-Fair st b (later e) = later (xdcoiter-Fair st _ e)

E-iter : ∀{A} {P : A → Set} {F : Stream A → Set} {B : Stream A → Set}
         (n : ∀ s → P (hd s) → F (tl s) → B s)
         (l : ∀ s → B (tl s) → B s) →
         ∀ s → E P F s → B s
E-iter n l s (now p f) = n s p f
E-iter n l s (later e) = l s (E-iter n l (tl s) e)



{-
Ev-iter : ∀{A} {P : A → Set} {F : Stream A → Set} {B : Stream A → Set}
          (st : ∀ s → Fair P s → F s)
          (n : ∀ s → F (tl s) → B s)
          (l : ∀ s → B (tl s) → B s) →
          ∀ s → Eventually P s → B s
Ev-iter st n l s (now p f) = n s (st (tl s) f)
Ev-iter st n l s (later e) = l s (Ev-iter st n l (tl s) e)
-}

{-
Ev-iter : ∀{A} {P : A → Set} {B : Stream A → Set}
          (n : ∀ s → Fair P (tl s) → B s)
          (l : ∀ s → B (tl s) → B s) →
          ∀ s → Eventually P s → B s
Ev-iter n l s (now p f) = n s f
Ev-iter n l s (later e) = l s (Ev-iter n l (tl s) e)
-}

{-
Ev-ind : ∀{A} {P : A → Set} (F : (t : Stream A) → Set)
         (B : (t : Stream A) → Eventually P t → Set)
         (st : ∀{t} → Fair P t → F t)
         (n : ∀{t} → (p : P (hd t)) → (f : F (tl t)) → B t (now p f)) →
         (l : ∀{t e} → B (tl t) e → B t (later e)) →
         (s : Stream A) → (e : Eventually P s) → B s e
Ev-ind F B st n l s (now p f) =
  let r = n p {!st!}
  in {!!}
Ev-ind F B st n l s (later e) = l (Ev-ind F B st n l (tl s) e)
-}

filter : ∀{A} {P : A → Set} (s : Stream A) → Fair P s → Stream A
xfilter : ∀{A} {P : A → Set} (s : Stream A) → Eventually P s → Stream A

filter s p = xfilter s (step p)

hd (xfilter s (now p q)) = hd s
tl (xfilter s (now p q)) = filter (tl s) q
xfilter s (later p)      = xfilter (tl s) p

filter-find : ∀{A} {P : A → Set} (s : Stream A) →
              Eventually P s → A × ∃ (Fair P)
filter-find = E-iter (λ s p f → (hd s , tl s , f)) (λ s → id)

filter-h : ∀{A} {P : A → Set} → ∃ (Fair P) → A
filter-h (s , f) = proj₁ (filter-find s (step f))

filter-t : ∀{A} {P : A → Set} → ∃ (Fair P) → ∃ (Fair P)
filter-t {A} {P} (s , f) = proj₂ (filter-find s (step f))

filter' : ∀{A} {P : A → Set} → ∃ (Fair P) → Stream A
filter' = Stream-coiter filter-h filter-t

-- filter' : ∀{A} {P : A → Set} (s : Stream A) → Fair P s → Stream A
-- filter' s f = filter'' (s , f)

{-
filter-pres-fair : ∀{A} {P : A → Set} (u : ∃ (Fair P)) →
                   Fair P (filter' u)
filter-pres-fair u = {!!}

filter-always' : ∀{A} {P : A → Set} (u : ∃ (Fair P)) →
                 Always P (filter' u)
filter-always' {A} {P} (s , f) = Always-coiter {B = Fair P} {!!} {!!} (filter' (s , f)) {!!}

-}

filter-always' : ∀{A} {P : A → Set} (u : ∃ (Fair P)) →
                 Always P (filter' u)
filter-always' {A} {P} = Always-coind f
  where
    xf : (s : Stream A) (e : Eventually P s) → P (proj₁ (filter-find s e))
    xf s (now p _) = p
    xf s (later e) = xf (tl s) e

    f : (u : ∃ (Fair P)) → P (filter-h u)
    f (s , f) = xf s (step f)


filter-always : ∀{A} {P : A → Set} (s : Stream A) → (f : Fair P s) →
                Always P (filter s f)
xfilter-always : ∀{A} {P : A → Set} (s : Stream A) → (e : Eventually P s) →
                 Always P (xfilter s e)

filter-always s f = xfilter-always s (step f)
hd-valid (xfilter-always s (now p f)) = p
tl-valid (xfilter-always s (now p f)) = filter-always (tl s) f
xfilter-always s (later e)            = xfilter-always (tl s) e

{-
filter-pres : ∀{A} {P Q : A → Set} (s : Stream A) → (f : Fair P s) →
              Always Q s → Always Q (filter s f)
xfilter-pres : ∀{A} {P Q : A → Set} (s : Stream A) → (e : Eventually P s) →
               Always Q s → Always Q (xfilter s e)

filter-pres s f a = xfilter-pres s (step f) a

xfilter-pres = {!!}
-}
-- xfilter-pres {Q = Q} s e a =
--   Ev-ind (λ t e → Always Q (xfilter t e))
--          (λ p f → record { hd-valid = {!hd-valid a!} ; tl-valid = {!!} })
--          {!!}
--          s
--          e

{-
hd-valid (xfilter-pres s (now p f) a) = hd-valid a
tl-valid (xfilter-pres s (now p f) a) = filter-pres (tl s) f (tl-valid a)
xfilter-pres s (later e) a = xfilter-pres (tl s) e (tl-valid a)
-}
