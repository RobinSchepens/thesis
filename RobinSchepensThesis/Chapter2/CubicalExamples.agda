{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce --allow-unsolved-metas  #-}

module CubicalExamples where

open import Bridgy.Core.BridgePrims

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism 
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

data _≡'_ {A : Type} : A → A → Type where
  refl' : {a : A} → a ≡' a

reflex : {A : Type} (x : A) → (x ≡ x)
reflex x = λ i → x

cong' : {A : Type} {B : A → Type} {x y : A} (f : (a : A) → B a) (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
cong' f p i = f(p i)

curryEquiv' : {A B C : Type} → ((A × B) → C) ≃ (A → B → C)
curryEquiv' = isoToEquiv (iso curry uncurry (λ x → refl) (λ x → refl))

module SIPSigma (A : Type) (B : A → Type) where

  obsEqΣ : Σ A B → Σ A B → Type
  obsEqΣ (a0 , b0) (a1 , b1) =
    Σ (a0 ≡ a1) (λ p → PathP (λ i → B (p i)) b0 b1)

  SIPΣ : (pair0 pair1 : Σ A B) → obsEqΣ pair0 pair1 ≃ (pair0 ≡ pair1)
  SIPΣ (a0 , b0) (a1 , b1) = isoToEquiv (iso obsToPath pathToObs
   (λ x → refl) (λ x → refl))

    where

      obsToPath : obsEqΣ (a0 , b0) (a1 , b1) → ((a0 , b0) ≡ (a1 , b1))
      obsToPath (p0 , p1) = λ i → p0 i , p1 i

      pathToObs : (a0 , b0) ≡ (a1 , b1) → obsEqΣ (a0 , b0) (a1 , b1)
      pathToObs p = (λ i → p i .fst) , λ i → p i .snd
