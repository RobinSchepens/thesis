{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module DataTypes where

open import Bridgy.Core.BridgePrims

data ⊥ : Type where

data Unit : Type where
  tt : Unit

data Bool : Type where
  true : Bool
  false : Bool

data ℕ : Type where
  zero : ℕ
  suc : ℕ → ℕ

data List (A : Type) : Type where
  [] : List A
  _∷_ : A → List A → List A

map : {A B : Type} → (A → B) → (List A → List B)
map f [] = []
map f (a ∷ as) = f a ∷ map f as

concat : {A : Type} → List A → List A → List A
concat [] as1 = as1
concat (a ∷ as0) as1 = a ∷ (concat as0 as1)

data Σ' (A : Type) (B : A → Type) : Type where
  _,_ : (a : A) → (b : B a) → Σ' A B

data _×_ (A B : Type) : Type where
   _,_ : (a : A) → (b : B) → A × B

curry : {A B C : Type} → ((A × B) → C) → (A → B → C)
curry f a b = f (a , b)

uncurry : {A B C : Type} → (A → B → C) → ((A × B) → C)
uncurry f (a , b) = f a b

data _⊎_ (A B : Type) : Type where
  left : A → A ⊎ B
  right : B → A ⊎ B

ℤ : Type
ℤ = ℕ ⊎ ℕ




