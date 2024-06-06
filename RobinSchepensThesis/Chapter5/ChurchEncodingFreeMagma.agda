{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module ChurchEncodingFreeMagma where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.GelExamples
open import Bridgy.Core.BDisc
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.Param
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.List


module _ {l : Level} (A : Type l) (isbA : isBDisc A) where

  data FMag : Type l where
    gen : A → FMag
    op : FMag → FMag → FMag

  

  Magma : Type (ℓ-suc l)
  Magma = Σ (Type l) λ X → (X → X → X)

  FMagAsMagma : Magma
  FMagAsMagma = FMag , op
  
  FMagChurch : Type (ℓ-suc l)
  FMagChurch = ∀ (M : Magma) → ((A → M .fst) → M .fst)

  
  -- ---------
  -- left and right maps
  -- same than usual
  -- ---------

  --defined by recursion (FMag is a data type).
  dataToChurch : FMag → FMagChurch
  dataToChurch (gen a) (Mcr , Mop) Mgen = Mgen a
  dataToChurch (op e1 e2) (Mcr , Mop) Mgen = Mop (dataToChurch e1 (Mcr , Mop) Mgen) (dataToChurch e2 (Mcr , Mop) Mgen)

  --defined by applying the input k to the free magma
  churchToData : FMagChurch → FMag
  churchToData k = k (FMag , op) gen
  
  Retract : ∀ (fmag : FMag) → churchToData (dataToChurch fmag) ≡ fmag
  Retract (gen a) = refl
  Retract (op e1 e2) = cong₂ op (Retract e1) (Retract e2)


 -- First we prove that the domain (Magma) is an NRG

 -- (X : Type l) ctx    (TypeNRG l) (NRG l+1)

 -- X ⊧ X               (X ⊧ ElX) (DispNRG l over NRG l+1)

 -- X ⊧ X               (X ⊧ ElX) (DispNRG l over NRG l+1)

 -- X ⊧ X → X           (→Form) (DispNRG l over NRG l+1)

 -- X ⊧ X → (X → X)     (→Form) (DispNRG l over NRG l+1) 

-- (Σ(X : Type l) X → (X → X) : Type l+1) ctx     (ctx-ext #) (NRG l+1) (MagmaNRG)


  Type⊨X→X→X : DispNRG l (TypeNRG l)
  Type⊨X→X→X = →Form l l (X⊨ElX) (→Form l l X⊨ElX X⊨ElX)

  MagmaNRG : NRGraph (ℓ-suc l)
  MagmaNRG = TypeNRG l # Type⊨X→X→X

 -- Now we prove that (A → X) → X is a dRRG over Magma

 -- (X : Type) ⊧ A                 (bDisc-asDNRG) ( DispNRG l over NRG l+1) (Type⊨A)

 -- X → X             (X ⊧ ElX) (DispNRG l over NRG l+1)
 
 -- X ⊧ A → X         (→Form) (DispNRG l over NRG l+1)

 -- X ⊧ (A → X) → X   (→Form) (DispNRG l over NRG l+1) (Type⊨A→X→X)

 -- MagmaNRG ⊨ (A → X) → X  (wkn) (DispNRG l over NRG l+1) (MagmaDNRG)

  Type⊨A : DispNRG l (TypeNRG l)
  Type⊨A = bDisc-asDNRG A isbA

  Type⊨A→X→X : DispNRG l (TypeNRG l)
  Type⊨A→X→X = →Form l l (→Form l l Type⊨A X⊨ElX) (X⊨ElX)

  MagmaDNRG : DispNRG l (MagmaNRG)
  MagmaDNRG = wkn Type⊨A→X→X

  edge-FMagAsMagma-M : (M : Magma) (f : A → M .fst) → MagmaNRG .nedge FMagAsMagma M
  edge-FMagAsMagma-M M f = (λ fmag m → (dataToChurch fmag M f) ≡ m) , λ fmag0 m0 hyp0 fmag1 m1 hyp1 → cong₂ (M .snd) hyp0 hyp1

  Section : ∀ (k : FMagChurch) → dataToChurch (churchToData k) ≡ k
  Section = λ k → funExt λ (M : Magma) → funExt λ (f : A → M .fst) →
    param MagmaNRG MagmaDNRG k FMagAsMagma M (edge-FMagAsMagma-M M f) gen f (λ a0 a1 eq → cong f eq)
      
  isoMagmaChurch : FMag ≃ FMagChurch
  isoMagmaChurch = isoToEquiv (iso dataToChurch churchToData Section Retract)

  


