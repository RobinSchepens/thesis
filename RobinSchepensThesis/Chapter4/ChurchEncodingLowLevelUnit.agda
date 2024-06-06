{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module ChurchEncodingLowLevelUnit where

open import Bridgy.Core.BridgePrims  
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.Data.Bool

f : ((X : Type) → X → X) → Unit
f = λ a → tt

g : Unit → ((X : Type) → X → X)
g = λ tt → (λ X → λ x → x)

Retract : (tt : Unit) → f (g tt) ≡ tt
Retract = λ tt → refl

module ChurchUnit (k : ∀ (X : Type) → X → X) (A : Type) (a : A ) where

   R : Unit → A → Type
   R tt a' = a  ≡ a'

   kGel : (@tick x : BI) → primGel Unit A R x → primGel Unit A R x
   kGel = λ x → k (primGel Unit A R x)

   gel : (@tick x : BI) → primGel Unit A R x
   gel = λ x → prim^gel tt a refl x

   asBridge : BridgeP (λ x → primGel Unit A R x) (k Unit tt) (k A a)
   asBridge = λ x → kGel x (gel x)

   ungel : R (k Unit tt) (k A a)
   ungel = prim^ungel (λ x → asBridge x)

open ChurchUnit public

Section : (k : (X : Type) → X → X) → g (f k) ≡ k
Section = λ k → funExt λ A → funExt λ a → ungel k A a

unitEquivChurch : ((X : Type) → X → X) ≃  Unit
unitEquivChurch = isoToEquiv (iso f g Retract Section)
