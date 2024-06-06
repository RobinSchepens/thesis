{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module PremonadExamples where

open import Bridgy.Core.BridgePrims

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.List 
open import Cubical.Data.Sigma

postulate
 l : Level

giveFirstVal : (X : Type l) → List X → X
giveFirstVal X (x ∷ xs) = x
giveFirstVal X [] = {!!}

data Maybe (X : Type l) : Type l where
  just : X → Maybe X
  nothing : Maybe X

giveFirstVal' : (X : Type l) → List X → Maybe X
giveFirstVal' X (x ∷ xs) = just x
giveFirstVal' X [] = nothing


MaybeBind : (X Y : Type l) → Maybe X → (X → Maybe Y) → Maybe Y
MaybeBind X Y (just x) = λ f → f x
MaybeBind X Y nothing = λ f → nothing

record PMnd : Type (ℓ-suc l) where  
  field
    pmnd : Type l → Type l
    ret : (X : Type l) → X → pmnd X
    bind : (X Y : Type l) → pmnd X → (X → pmnd Y) → pmnd Y
open PMnd public 

MaybePmnd : PMnd
MaybePmnd = record {
  pmnd = λ X → Maybe X ;
  ret = λ X x → just x ;
  bind = MaybeBind }


IdPmnd : PMnd
IdPmnd = record {
  pmnd = λ X → X ;
  ret = λ X x → x ;
  bind = λ X Y x f → f x}

concat : {A : Type l} → List A → List A → List A
concat [] as1 = as1
concat (a ∷ as0) as1 = a ∷ (concat as0 as1)

ListPmnd : PMnd
ListPmnd = record {
  pmnd = λ X → List X ;
  ret = λ X x → x ∷ [] ;
  bind = ListBind }

    where

    ListBind : (X Y : Type l) → List X → (X → List Y) → List Y
    ListBind X Y (x ∷ xs) = λ f → concat (f x) (ListBind X Y xs f)
    ListBind X Y [] = λ f → []    

record PMndMorphism (κ0 κ1 : PMnd) : Type (ℓ-suc l) where
  field
    morph : (X : Type l) → κ0 .pmnd X → κ1 .pmnd X 
    morphRet : (X : Type l) (x : X) → morph X (κ0 .ret X x) ≡ κ1 .ret X x  
    morphBind :  (X Y : Type l) (κx0 : κ0 .pmnd X) (k : X → κ0 .pmnd Y) → morph Y (κ0 .bind X Y κx0 k) ≡ κ1 .bind X Y (morph X κx0) ((morph Y) ∘ k)
open PMndMorphism public 
