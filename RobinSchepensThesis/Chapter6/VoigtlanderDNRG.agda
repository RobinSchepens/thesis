{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module VoigtlanderDNRG where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.GelExamples
open import Bridgy.Core.BDisc
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.Param
open import Bridgy.ROTT.MoreVarRules
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.List



postulate
  l : Level

record preMonad  : Type (ℓ-suc l) where
  field
    M : Type l → Type l
    return : {X : Type l} → X → M X
    bind : {A B : Type l} → M A → (A → M B) → M B
open preMonad public

  

Unit⊨Type→Type : DispNRG (ℓ-suc l) topNRG
Unit⊨Type→Type = →Form (ℓ-suc l) (ℓ-suc l) (UForm l) (UForm l)


Unit,Type→Type : NRGraph (ℓ-suc l)
Unit,Type→Type = topNRG # Unit⊨Type→Type


Unit,Type→Type⊨Type : DispNRG (ℓ-suc l) Unit,Type→Type
Unit,Type→Type⊨Type = UForm l


Unit,Type→Type,Type : NRGraph (ℓ-suc l)
Unit,Type→Type,Type = Unit,Type→Type # Unit,Type→Type⊨Type


Unit,Type→Type,Type⊨X : DispNRG l Unit,Type→Type,Type
Unit,Type→Type,Type⊨X = El (let v =  var0 Unit,Type→Type Unit,Type→Type⊨Type in record {tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ})

Unit,Type→Type,Type⊨MX : DispNRG l Unit,Type→Type,Type
Unit,Type→Type,Type⊨MX = El (app Unit,Type→Type,Type (UForm l) (UForm l) (let v = var1 Unit⊨Type→Type Unit,Type→Type⊨Type in record {tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ}) (let v =  var0 Unit,Type→Type Unit,Type→Type⊨Type in record {tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ}))

retDNRG : DispNRG (ℓ-suc l) Unit,Type→Type
retDNRG = ΠForm Unit,Type→Type⊨Type (→Form l l Unit,Type→Type,Type⊨X Unit,Type→Type,Type⊨MX)

Unit,Type→Type,Type⊨Type : DispNRG (ℓ-suc l) Unit,Type→Type,Type
Unit,Type→Type,Type⊨Type = UForm l

Unit,Type→Type,Type,Type : NRGraph (ℓ-suc l)
Unit,Type→Type,Type,Type = Unit,Type→Type,Type # Unit,Type→Type,Type⊨Type

Unit,Type→Type,Type,Type⊨MX : DispNRG l Unit,Type→Type,Type,Type
Unit,Type→Type,Type,Type⊨MX = El (app Unit,Type→Type,Type,Type (UForm l) (UForm l) (let v = var2 topNRG Unit⊨Type→Type Unit,Type→Type⊨Type Unit,Type→Type,Type⊨Type in record {tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }) (let v = var1 Unit,Type→Type⊨Type Unit,Type→Type,Type⊨Type in record {tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ}))

Unit,Type→Type,Type,Type⊨MY : DispNRG l Unit,Type→Type,Type,Type
Unit,Type→Type,Type,Type⊨MY = El (app Unit,Type→Type,Type,Type (UForm l) (UForm l) (let v = var2 topNRG Unit⊨Type→Type Unit,Type→Type⊨Type Unit,Type→Type,Type⊨Type in record {tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }) (let v = var0 Unit,Type→Type,Type Unit,Type→Type,Type⊨Type in record {tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ}))

Unit,Type→Type,Type,Type⊨X : DispNRG l Unit,Type→Type,Type,Type
Unit,Type→Type,Type,Type⊨X = El (let v = var1 Unit,Type→Type⊨Type Unit,Type→Type,Type⊨Type in record {tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })

bindDNRG : DispNRG (ℓ-suc l) Unit,Type→Type
bindDNRG = ΠForm Unit,Type→Type⊨Type (ΠForm Unit,Type→Type,Type⊨Type (→Form l l Unit,Type→Type,Type,Type⊨MX (→Form l l (→Form l l Unit,Type→Type,Type,Type⊨X Unit,Type→Type,Type,Type⊨MY) Unit,Type→Type,Type,Type⊨MY)))

Unit,Type→Type⊨ret×bind : DispNRG (ℓ-suc l) Unit,Type→Type
Unit,Type→Type⊨ret×bind = (×Form (ℓ-suc l) (ℓ-suc l) retDNRG bindDNRG)

premonRRG : NRGraph (ℓ-suc l)
premonRRG = Unit,Type→Type # Unit,Type→Type⊨ret×bind

--First dRRG for theorems 1-4

postulate
  A : Type l
  isbA : isBDisc A
  

Unit,Type→Type⊨A : DispNRG l Unit,Type→Type
Unit,Type→Type⊨A = bDisc-asDNRG A isbA

Unit,Type→Type⊨MA : DispNRG l Unit,Type→Type
Unit,Type→Type⊨MA = El (app Unit,Type→Type (UForm l) (UForm l) (let v = var0 topNRG Unit⊨Type→Type in record {tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ}) (code Unit,Type→Type⊨A))

Unit,Type→Type⊨ListMA : DispNRG l Unit,Type→Type
Unit,Type→Type⊨ListMA = ListdNRG' Unit,Type→Type⊨MA

Unit,Type→Type⊨ListMA→MA : DispNRG l Unit,Type→Type
Unit,Type→Type⊨ListMA→MA = →Form l l Unit,Type→Type⊨ListMA Unit,Type→Type⊨MA

voigtdRRG : DispNRG l premonRRG
voigtdRRG = wkn Unit,Type→Type⊨ListMA→MA

--Second dRRG for theorem 5

Unit,Type→Type,Type⊨ListMX : DispNRG l Unit,Type→Type,Type
Unit,Type→Type,Type⊨ListMX = ListdNRG' Unit,Type→Type,Type⊨MX

Unit,Type→Type,Type⊨MListX : DispNRG l Unit,Type→Type,Type
Unit,Type→Type,Type⊨MListX = El (app Unit,Type→Type,Type (UForm l) (UForm l) (let v = var1 Unit⊨Type→Type Unit,Type→Type⊨Type in record {tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ} ) (code (ListdNRG' Unit,Type→Type,Type⊨X)))

Unit,Type→Type,Type⊨ListMX→MListX : DispNRG l Unit,Type→Type,Type
Unit,Type→Type,Type⊨ListMX→MListX = →Form l l Unit,Type→Type,Type⊨ListMX Unit,Type→Type,Type⊨MListX

voigtdRRG2 : DispNRG (ℓ-suc l) premonRRG
voigtdRRG2 = wkn (ΠForm (UForm l) Unit,Type→Type,Type⊨ListMX→MListX)
