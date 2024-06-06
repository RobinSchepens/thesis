{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module ChurchEncodingLowLevelNat where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.ExtentExamples
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Nat


-- Want to prove ℕ ≃ (X : Type) → (X → X) → X → X
-- Use isoToEquiv Lemma to prove equivalence, need : f : A → B , g = B → A , g ∘ f ≡ id , f ∘ g ≡ id

leftToRight : ℕ → ∀ (X : Type) → (X → X) → X → X
leftToRight zero = λ X → λ f → λ x → x
leftToRight (suc n) = λ X → λ f → λ x → f (leftToRight n X f x)

rightToLeft : (∀ (X : Type) → (X → X) → X → X) → ℕ
rightToLeft k  = k ℕ suc zero

retract' : ∀ (n : ℕ) → rightToLeft (leftToRight n) ≡ n
retract' zero = refl
retract' (suc n) = cong suc (retract' n)

module ParametricityNat (k : ∀ (X : Type) → (X → X) → X → X) (A : Type) (f : A → A) (y : A) where 

  R : ℕ → A → Type
  R n a = leftToRight n A f y ≡ a --graph relation

  kGelx : (@tick x : BI) → (primGel ℕ A R x → primGel ℕ A R x) → primGel ℕ A R x → primGel ℕ A R x
  kGelx = λ x → k (primGel ℕ A R x)

  relatedZero : (@tick x : BI) → primGel ℕ A R x
  relatedZero = λ x → prim^gel zero y refl x

  relatedFun : ∀ (n : ℕ) (a : A) → R n a → R (suc n) (f a)
  relatedFun n a inductionHyp = cong f inductionHyp

  --primExtent : ∀ {A B : Type} {A : (@tick x : BI) → Type} {B : (@tick x : BI) (a : A x) → Type}
  --(N0 : (a0 : A bi0) → B bi0 a0) (N1 : (a1 : A bi1) → B bi1 a1) (NN : (a0 : A bi0) (a1 : A bi1)
  --(aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1)
  --(@tick r : BI) (M : A r) → B r M
  --With A = λ x → primGel ℕ A R x and B non dependent of a : A x
  --With N0 = suc : ℕ → ℕ , N1 = f : A → A, NN = pointwiseBridge

  pointwiseRelated : (n : ℕ) (a : A) (aa : BridgeP (λ x → primGel ℕ A R x) n a) → R (suc n) (f a)
  pointwiseRelated n a aa = relatedFun n a  (prim^ungel (λ x → aa x))

 
  pointwiseBridge : (n : ℕ) (a : A) (aa : BridgeP (λ x → primGel ℕ A R x) n a) → BridgeP (λ x → primGel ℕ A R x) (suc n) (f a)
  pointwiseBridge n a aa = λ x → prim^gel (suc n) (f a) (pointwiseRelated n a aa) x

  primGelToprimGel : (@tick r : BI) → (M : primGel ℕ A R r) → primGel ℕ A R r
  primGelToprimGel = primExtent suc f pointwiseBridge

  kgelx-fungel-gel : (@tick x : BI) → primGel ℕ A R x
  kgelx-fungel-gel = λ x → kGelx x (primGelToprimGel x ) (relatedZero x)

  asBridge : BridgeP (λ x → primGel ℕ A R x) (k ℕ suc zero) (k A f y)
  asBridge = λ x → kgelx-fungel-gel x

  ungel : R (k ℕ suc zero) (k A f y)
  ungel = prim^ungel (λ x → asBridge x)
  
  
open ParametricityNat public

section' : ∀ (k : ∀ (X : Type) → (X → X) → X → X) → leftToRight (rightToLeft k) ≡ k
section' = λ k → funExt λ A → funExt λ f → funExt λ y → ParametricityNat.ungel k A f y

--Final goal: leftToRight (rightToLeft k) A f x ≡ k A f x

natIsoChurch : ℕ  ≃ ∀ (X : Type) → (X → X) → X  → X
natIsoChurch = isoToEquiv (iso leftToRight rightToLeft section' retract')
