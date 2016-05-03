{-

A possible implementation of the following HIT arr. Note that this type is
mutually defined with App, that is to say, they are defined by
induction-recursion!

Inductive arr (A,B:Set) : Set :=
| base : B -> arr A B
| step : (A -> arr A B) -> arr A B.
| path : (forall x : A, App f x = App g x) -> f = g.

where App is defined by

Fixpoint App (f : arr A B)(a : A) :=
match f with
| base b => b
| step g => App (g a) a
end.

Due to the fact that arr and App are defined by induction-recuriosn, the
recursion principle for arr needs to make extra assumptions, see the parameters
of the arr-Rec module.
Effectively, we see the function space A → B as algebra for the functor (-) × A
and App is an algebra homomorphism from arr A B to A → B.
This is reflected in the extra assumption in the recursion principle.

-}


{-# OPTIONS --without-K #-}
open import lib.Basics
open import lib.PathGroupoid
open import lib.types.Paths
open import lib.Funext


module _ where
  private
    data #arr-aux (A B : Set) : Set where
      #base : B → #arr-aux A B
      #step : (A → #arr-aux A B) → #arr-aux A B

    #App : ∀{A B} → #arr-aux A B → A → B
    #App (#base b) a = b
    #App (#step g) a = #App (g a) a

  _~>_ : Set → Set → Set
  _~>_ = #arr-aux

  base : ∀{A B} → B → A ~> B
  base = #base

  step : ∀{A B} → (A → A ~> B) → A ~> B
  step = #step

  App : ∀{A B} → A ~> B → A → B
  App = #App

  Abstr : ∀{A B} → (A → B) → A ~> B
  Abstr f = step (λ x → base (f x))

  postulate
    path : ∀{A B} (f g : A ~> B) (a : A) → App f a == App g a → f == g

  module arr-Rec {A B X : Set}
    (base* : B → X)
    (step* : (A → X) → X)
    (App* : X → A → B)
    -- Here we need to make the assumption that App* is an algebra homomorphism
    -- from X into the function space.
    (App*-β₂ : (a : A) (f : A → X) → App* (step* f) a == App* (f a) a)
    (path* : (x y : X) (a : A) → App* x a == App* y a → x == y)
    where
    rec : A ~> B → X
    rec = rec-aux phantom where
      rec-aux : Phantom path* → A ~> B → X
      rec-aux ph (#base b) = base* b
      rec-aux ph (#step f) = step* (λ a → rec-aux ph (f a))

    lem : (f g : A ~> B) (a : A) →
      App f a == App g a → App* (rec f) a == App* (rec g) a
    lem (#base b) (#base .b) a idp = idp
    lem (#base b) (#step g) a p =
      let β-red* = App*-β₂ a (rec ∘ g)
          IH = lem (#base b) (g a) a p
      in  IH ∙ ! β-red*
    lem (#step f) (#base b) a p =
      let β-red* = App*-β₂ a (rec ∘ f)
          IH = lem (f a) (#base b) a p
      in  β-red* ∙ IH
    lem (#step f) (#step g) a p =
      let IH = lem (f a) (g a) a p
          β-red-f = App*-β₂ a (rec ∘ f)
          β-red-g = App*-β₂ a (rec ∘ g)
      in β-red-f ∙ IH ∙ ! β-red-g

    postulate
      path-β : (f g : A ~> B) (a : A) (p : App f a == App g a) →
               ap rec (path f g a p)
               == path* (rec f) (rec g) a (lem f g a p)
