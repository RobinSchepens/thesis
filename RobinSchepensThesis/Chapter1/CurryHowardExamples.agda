{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module CurryHowardExamples where

open import Bridgy.Core.BridgePrims
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

noContradictions : (P : Type) →  P × (P → ⊥) → ⊥
noContradictions P (p , f) = f p

_>_ : ℕ → ℕ → Type
zero > zero = ⊥
suc m > zero = Unit
zero > suc n = ⊥
suc m > suc n = m > n

lemma : (n : ℕ) → suc n > n
lemma zero = tt
lemma (suc n) = lemma n

noUpperBound : (n : ℕ) → Σ ℕ (λ m → (m > n))
noUpperBound zero = suc zero , tt
noUpperBound (suc n) = suc (suc n) , lemma n
