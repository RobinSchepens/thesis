{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce --allow-unsolved-metas  #-}

module IntroParametricity where

open import Bridgy.Core.BridgePrims

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

f : ((X : Type) → X → X) → Unit
f = λ a → tt

g : Unit → ((X : Type) → X → X)
g = λ tt → (λ X → λ x → x)

retract : (tt : Unit) → f (g tt) ≡ tt
retract = λ tt → refl

section : (k : (X : Type) → X → X) → g (f k) ≡ k
section = λ k → funExt λ A → funExt λ a → {!!}

