{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}


module ChurchEncodingUnitSRP where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.GelExamples renaming (bdg-over-gel to primGelSRP)
open import Bridgy.Core.BDisc
open import Bridgy.Core.ExtentExamples renaming (ΠvsBridgeP to extentEquiv) 
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

postulate
  l : Level

bareParam : {A : Type (ℓ-suc ℓ-zero)} {B : A → Type ℓ-zero} {a0 a1 : A} (f : (a : A) → B a) (aa : Bridge A a0 a1) → BridgeP (λ x → B (aa x)) (f a0) (f a1)
bareParam f aa = λ x → f(aa x)


module UnitChurch (k : ∀ (X : Type) → X → X) (A : Type) (a : A) where

  R : Unit → A → Type 
  R tt a' = a ≡ a'

  bdgDomain : Bridge Type Unit A
  bdgDomain = equivFun relativity R 

  bdgCodomain : BridgeP (λ x → (primGel Unit A R x → primGel Unit A R x))
    (k Unit) (k A) 
  bdgCodomain = bareParam k bdgDomain

  bdg→bdg : (tt : Unit) (a0 : A) (aa : BridgeP (λ x → primGel Unit A R x) tt a0)
    → BridgeP (λ x → primGel Unit A R x) (k Unit tt) (k A a0)
  bdg→bdg = invEq extentEquiv bdgCodomain

  bdg-tt-a : BridgeP (λ x → primGel Unit A R x) tt a
  bdg-tt-a = invEq (primGelSRP R tt a) refl

  bdg-ktt-ka : BridgeP (λ x → primGel Unit A R x) (k Unit tt) (k A a)
  bdg-ktt-ka = bdg→bdg tt a bdg-tt-a

  toRel : R (k Unit tt) (k A a)
  toRel = equivFun (primGelSRP R (k Unit tt) (k A a)) bdg-ktt-ka

