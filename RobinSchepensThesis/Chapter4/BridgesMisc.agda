{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module BridgesMisc where

open import Bridgy.Core.BridgePrims
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty
open import Cubical.Data.Sigma


module _ {ℓ} (A : (@tick x : BI) → Type ℓ) (a0 : A bi0) (a1 : A bi1) where

  elimBridge : (aa : BridgeP A a0 a1) (@tick x : BI) → A x
  elimBridge aa x = aa x

  -- elimBridge' : (x : BI) (aa : BridgeP A a0 a1) → A x
  -- elimBridge' x aa = aa x

reflBdg : {A : Type} (a : A) → Bridge A a a
reflBdg a = λ x → a

bareParam : {A : Type} {B : A → Type} {a0 a1 : A}
  (f : (a : A) → B a) (aa : Bridge A a0 a1) →
  BridgeP (λ x → B (aa x)) (f a0) (f a1)
bareParam f aa = λ x → f (aa x)

module SRPSigma (A : Type) (B : A → Type) where

  logRelSigma : Σ A B → Σ A B → Type
  logRelSigma (a0 , b0) (a1 , b1) =
    Σ (Bridge A a0 a1) (λ aa → BridgeP (λ i → B (aa i)) b0 b1)

ListRCover : {A0 A1 : Type} (R : A0 → A1 → Type) → List A0 → List A1
  → Type
ListRCover R [] [] = Unit
ListRCover R [] (a1 ∷ as1) = ⊥
ListRCover R (a0 ∷ as1) [] = ⊥
ListRCover R (a0 ∷ as0) (a1 ∷ as1) = R a0 a1 × ListRCover R as0 as1

hasBDisc : (A : Type) → Type 
hasBDisc A = (a0 a1 : A) →  (a0 ≡ a1) ≃ (Bridge A a0 a1)

