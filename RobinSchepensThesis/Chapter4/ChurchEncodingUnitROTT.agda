{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module ChurchEncodingUnitROTT where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.GelExamples
open import Bridgy.Core.BDisc
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules renaming (→Form to SomethingElse)
open import Bridgy.ROTT.Param
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.List
open import myROTTRules

postulate
  l : Level

--Want to prove (X : Type) → X → X ≃ Unit

f : ((X : Type l) → X → X) → Unit
f = λ a → tt

g : Unit → ((X : Type l) → X → X)
g = λ tt → (λ X → λ x → x)

Retract : (tt : Unit) → f (g tt) ≡ tt
Retract = λ tt → refl

module ParametricityUnit (k : ∀ (X : Type l) → X → X) (A : Type l) (a : A ) where

  R : (Lift {ℓ-zero} {l} Unit) → A → Type l
  R (lift tt) a' = a ≡ a'

  domainNRG : NRGraph (ℓ-suc l)
  domainNRG = TypeNRG l  

  codomainDNRG : DispNRG l domainNRG
  codomainDNRG = →Form X⊨ElX X⊨ElX

  dispLogRel : (tt : Lift Unit) (a : A) → (R tt a) → R (k (Lift Unit) tt) (k A a)
  dispLogRel = param domainNRG codomainDNRG k (Lift Unit) A R

  theorem : R (k (Lift Unit) tt*) (k A a)
  theorem = dispLogRel (lift tt) a refl
