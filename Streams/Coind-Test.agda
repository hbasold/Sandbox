open import Relation.Binary.PropositionalEquality as P
open import Function
open import Streams

tl' : ∀{A} → Stream A → Stream A
tl' s = tl s

coind : ∀{A X : Set} → (f g : X → Stream A) →
        hd ∘ f ≡ hd ∘ g →
        (u : ?) →
        ((v : ∀ x → f x ~ g x) → v ∘ u 
        ∀ x → f x ~ g x
hd~ (coind f g p x) = cong-app p x
tl~ (coind f g p x) = coind (tl' ∘ f) (tl' ∘ g) {!!} {!!}
