module Productive where

open import Stream
open import Size
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality as P

PStream : Set → Set
PStream A = Stream (Maybe A)

mutual
  record Productive {A : Set} (s : PStream A) : Set where
    coinductive
    field
      step : EventualOutput s

  data EventualOutput {A : Set} (s : PStream A) : Set where
    here  : (a : A) → s .hd ≡ just a  → Productive (s .tl)     → EventualOutput s
    there :           s .hd ≡ nothing → EventualOutput (s .tl) → EventualOutput s

open Productive public

ProdStr : Set → Set
ProdStr A = Σ[ s ∈ PStream A ] (Productive s)

injS : {A : Set} → Stream A → ProdStr A
injS {A} s = (toPStream s , prod s)
  where
    toPStream : Stream {∞} A → PStream A
    toPStream s .hd = just (s .hd)
    toPStream s .tl = toPStream (s .tl)

    prod : (s : Stream A) → Productive (toPStream s)
    prod s .step = here (s .hd) refl (prod (s .tl))

extract  : {A : Set} → ProdStr A → Stream A
extract (s , p) = extr s p
  where
    extr  : {A : Set} → (s : PStream A) → Productive s → Stream A
    extrμ  : {A : Set} → (s : PStream A) → EventualOutput s → Stream A

    extr {A} s p = extrμ s (p .step)

    extrμ {A} s (here a q p') .hd = a
    extrμ {A} s (here a q p') .tl = extr (s .tl) p'
    extrμ {A} s (there x p')      = extrμ (s .tl) p'

zipS : ∀{A} → ProdStr A → ProdStr A → ProdStr A
zipS {A} (s , p) (t , q) = (z s t , pz p q)
  where
    z : PStream A → PStream A → PStream A
    cz : Maybe A → PStream A → PStream A → PStream A

    z s t = cz (s .hd) (s .tl) t

    cz (just a) s' t .hd = just a
    cz (just a) s' t .tl = z t s'
    cz nothing  s' t .hd = nothing
    cz nothing  s' t .tl = cz (s' .hd) (s' .tl) t

    pz : {s t : PStream A} → Productive s → Productive t → Productive (z s t)
    pcz : {s t : PStream A} → Productive s → Productive t →
          Productive (cz (s .hd) (s .tl) t)
    pczE : {s t : PStream A} → EventualOutput s → Productive t →
           EventualOutput (cz (s .hd) (s .tl) t)
    pz p q = pcz p q

    pcz p q .step = pczE (p .step) q

    pczE {s} (here a s₀≡a p')  q with s .hd
    pczE {s} (here .a refl p') q | just a = here a refl (pz q p')
    pczE {s} (here a () p')    q | nothing
    pczE {s} (there s₀≡∗ p')   q with s .hd
    pczE {s} (there () p')     q | just a
    pczE {s} (there refl p')   q | nothing = there refl (pczE p' q)
