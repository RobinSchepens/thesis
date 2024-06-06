{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module VoigtlanderTheorems1-4 where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.List
open import Bridgy.Core.BridgeExamples
open import Bridgy.Core.ExtentExamples
open import Bridgy.Core.GelExamples
open import Bridgy.Core.EquGraph
open import Bridgy.Core.BDisc 
open import Bridgy.Core.MyPathToEquiv
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.Param

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Unit
open import Cubical.Data.List hiding ( [_] )
open import Cubical.Data.Sigma


open import VoigtlanderDNRG

PMnd : Type (ℓ-suc l)
PMnd = Σ (Type l → Type l) (λ pmnd → ((X : Type l) → X → pmnd X)
  × ((X Y : Type l) → pmnd X → (X → pmnd Y) → pmnd Y))

IdPmnd : PMnd
IdPmnd = (λ X → X) , (λ X x → x) , λ X Y mx k → k mx

--PMndMorphism : (κ0 κ1 : PMnd) → Type (ℓ-suc l)
--PMndMorphism κ0 κ1 = Σ ((X : Type l) → κ0 .fst X → κ1 .fst X) (λ morphism →
  --((X : Type l) (x : X) → morphism X (κ0 .snd .fst X x) ≡ κ1 .snd .fst X x)
  --× ((X Y : Type l) (κx0 : κ0 .fst X) (k : X → κ0 .fst Y) → morphism Y (κ0 .snd .snd X Y κx0 k) ≡ κ1 .snd .snd X Y (morphism X κx0)((morphism Y) ∘ k)))

record PMndMorphism (κ0 κ1 : PMnd) : Type (ℓ-suc l) where
  field
    morphism : (X : Type l) → κ0 .fst X → κ1 .fst X 
    morphismRet : (X : Type l) (x : X) → morphism X (κ0 .snd .fst X x) ≡ κ1 .snd .fst X x  
    morphismBind :  (X Y : Type l) (κx0 : κ0 .fst X) (k : X → κ0 .fst Y) → morphism Y (κ0 .snd .snd X Y κx0 k) ≡ κ1 .snd .snd X Y (morphism X κx0) ((morphism Y) ∘ k)
open PMndMorphism public

module theorem1
  (f : ∀ (M : premonRRG .nrg-cr) → List (M .fst .snd A) → M .fst .snd A)
  (κ : PMnd)
  (law1-κ : ∀ X Y (x : X) (k : X → κ .fst Y) → (κ .snd .snd X Y (κ .snd .fst X x) k) ≡ k x)
  where

  pureval : κ .fst A → Type l
  pureval κa = Σ A (λ a → κa ≡ κ .snd .fst A a)

  purelist : List (κ .fst A) → Type l
  purelist [] = Lift Unit
  purelist (ma ∷ mas) = pureval ma × (purelist mas)

  giveVals : (mas : List (κ .fst A)) (plis : purelist mas) → List A
  giveVals [] _ = []
  giveVals (ma ∷ mas) (pma , pmas) = (pma .fst) ∷ giveVals mas pmas

  --test : premoRRG .nrg-cr
  --test = {!!} , {!!} , {!!}

  edge-κ-Id : premonRRG .nedge ((tt , κ .fst) , κ .snd .fst , κ .snd .snd) ((tt , IdPmnd .fst) , IdPmnd .snd .fst , IdPmnd .snd .snd)
  edge-κ-Id = (tt , λ X0 X1 XX κx0 x1 → Σ X0 (λ x0 → (κ .snd .fst X0 x0 ≡ κx0) × (XX x0 x1))) ,
    (λ X0 X1 XX x0 x1 xx → x0 , refl , xx) ,
    λ X0 X1 XX Y0 Y1 YY κx0 x1 hyp k0 k1 hypk →
        let
          hypk-fwd : Σ Y0 (λ y0 → (κ .snd .fst Y0 y0 ≡ k0 (hyp .fst)) × YY y0 (k1 x1))
          hypk-fwd  = hypk (hyp .fst) x1 (hyp .snd .snd)
         
          dedct1 : κ .snd .fst X0 (hyp .fst) ≡ κx0
          dedct1 = hyp .snd .fst in

        hypk-fwd .fst ,
        ((hypk-fwd .snd .fst) ∙ (sym (law1-κ X0 Y0 (hyp .fst) k0)))
        ∙ cong (λ blank → κ .snd .snd X0 Y0 blank k0) dedct1  ,
        hypk-fwd .snd .snd


  voigt-thm1 : ∀ (mas : List (κ .fst A)) →
    purelist mas → pureval (f ((tt , κ .fst) , κ .snd .fst , κ .snd .snd) mas)
  voigt-thm1 mas plis =
    let
      partialParam = param premonRRG voigtdRRG f ((tt , κ .fst) , κ .snd .fst , κ .snd .snd) ((tt , IdPmnd .fst) , IdPmnd .snd .fst , IdPmnd .snd .snd) edge-κ-Id mas (giveVals mas plis) (aux mas plis)
    in
    partialParam .fst , sym (partialParam .snd .fst)

    where

      aux : ∀ mas plis →
       ListRCover
       (λ κx0 x1 → Σ A (λ x0 → (κ .snd .fst A x0 ≡ κx0) × Path A x0 x1)) mas
       (giveVals mas plis)
      aux [] _ = lift tt
      aux (ma ∷ mas) (pma , pmas) =
        (pma .fst , (sym (pma .snd)) , refl) ,
        aux mas pmas

module VOIGT2
  (f : ∀ (M : premonRRG .nrg-cr) → List (M .fst .snd A) → M .fst .snd A)
  (κ : PMnd)
  (p : ∀ (A : Type l) → κ .fst A → A)
  (eq1 : ∀ (X : Type l) (x : X) → (p X (κ .snd .fst X x)) ≡ x)
  (eq2 : ∀ (X : Type l) (Y : Type l) (κx : κ .fst X) (q : X → κ .fst Y) → p Y (κ .snd .snd X Y κx q) ≡ p Y (q (p X  κx)))
  where

  edge-κ-Id : premonRRG .nedge ((tt , κ .fst) , κ .snd .fst , κ .snd .snd) ((tt , IdPmnd .fst) , IdPmnd .snd .fst , IdPmnd .snd .snd)
  edge-κ-Id = (tt , λ X0 X1 XX κx0 x1 → Σ X0 (λ x0 → (p X0 κx0 ≡ x0) × (XX x0 x1))) ,
    (λ X0 X1 XX x0 x1 xx → x0 , eq1 X0 x0 , xx) ,
    λ X0 X1 XX Y0 Y1 YY κx0 x1 hyp k0 k1 hypk →
        let
          hypk-fwd : Σ Y0 (λ y0 → (p Y0 (k0 (hyp .fst)) ≡ y0) × YY y0 (k1 x1))
          hypk-fwd  = hypk (hyp .fst) x1 (hyp .snd .snd)
         
          dedct1 : p X0 κx0 ≡ hyp .fst
          dedct1 = hyp .snd .fst

          apEq2 : p Y0 (κ .snd .snd X0 Y0 κx0 k0) ≡ p Y0 (k0 (p X0 κx0))
          apEq2 = eq2 X0 Y0 κx0 k0 in

        hypk-fwd .fst ,
        sym (sym (cong (p Y0) (cong k0 dedct1) ∙ hypk-fwd .snd .fst) ∙ sym apEq2)  ,
        hypk-fwd .snd .snd
        
  voigt-thm2 : ∀ (mas : List (κ .fst A)) → p A (f ((tt , κ .fst) , κ .snd .fst , κ .snd .snd) mas) ≡ f ((tt , IdPmnd .fst) , IdPmnd .snd .fst , IdPmnd .snd .snd) (map (p A) mas)
  voigt-thm2 mas = 
    let
      partialParam = param premonRRG voigtdRRG f ((tt , κ .fst) , κ .snd .fst , κ .snd .snd) ((tt , IdPmnd .fst) , IdPmnd .snd .fst , IdPmnd .snd .snd) edge-κ-Id mas (map (p A) mas) (aux mas) 
    in
    partialParam .snd .fst ∙ partialParam .snd .snd

    where

      aux : ∀ (mas : List (κ .fst A)) → ListRCover (λ κx0 x1 → Σ A (λ x0 → (p A κx0 ≡ x0) × Path A x0 x1)) mas (map (p A) mas)
      aux [] = lift tt
      aux (ma ∷ mas) = (p A ma , refl , refl) , aux mas
   

module VOIGT3
  (f : ∀ (M : premonRRG .nrg-cr) → List (M .fst .snd A) → M .fst .snd A)
  (κ1 κ2 : PMnd) 
  (h : PMndMorphism κ1 κ2)
  where



  κ2ac : premonRRG .nedge ((tt , κ2 .fst) , κ2 .snd .fst , κ2 .snd .snd) ((tt , κ2 .fst) , κ2 .snd .fst , κ2 .snd .snd)
  κ2ac = invEq (premonRRG .nativ ((tt , κ2 .fst) , κ2 .snd .fst , κ2 .snd .snd) ((tt , κ2 .fst) , κ2 .snd .fst , κ2 .snd .snd) ) λ a → ((tt , κ2 .fst) , κ2 .snd .fst , κ2 .snd .snd)

  postulate

 
    isbdscA : isBDisc A
    isbκ2A : isBDisc (κ2 .fst A)
    κ2acnativrel : (g0 g1 : Type l) (gg : TypeNRG l ⦅ g0 , g1 ⦆) (gbdg : BridgeP (λ _ → Type l) g0 g1) → gg [ relativity ] gbdg → κ2ac .fst .snd g0 g1 gg [ relativity ] (λ x → κ2 .fst (gbdg x))

  κ2asNRelator : NRelator (TypeNRG l) (TypeNRG l)
  κ2asNRelator = record {
    nrel0 = κ2 .fst ;
    nrel1 = κ2ac .fst .snd ;
    nativ-rel = κ2acnativrel }

  edge-κ2-κ1 : premonRRG .nedge ((tt , κ2 .fst) , κ2 .snd .fst , κ2 .snd .snd) ((tt , κ1 .fst) , κ1 .snd .fst , κ1 .snd .snd)
  edge-κ2-κ1 = (tt , λ X0 X1 XX κ2x0 κ1x1 → Σ (κ2 .fst X1) (λ κ2x1 → (κ2ac .fst .snd X0 X1 XX κ2x0 κ2x1) × (κ2x1 ≡ h .morphism X1 κ1x1))) , (λ X0 X1 XX x0 x1 xx → κ2 .snd .fst X1 x1 , κ2ac .snd .fst X0 X1 XX x0 x1 xx , sym (h .morphismRet X1 x1)) ,
    ( λ X0 X1 XX Y0 Y1 YY κ2x0 κ1x1 hyp k0 k1 hypk → κ2 .snd .snd X1 Y1 (hyp .fst) (λ x1 → h .morphism Y1 (k1 x1)) ,
    κ2ac .snd .snd X0 X1 XX Y0 Y1 YY κ2x0 (hyp .fst) (hyp .snd .fst) k0 (λ x1 → h .morphism Y1 (k1 x1))
      (λ x0 x1 xx →

      let hypk-fwd = Σ (κ2 .fst Y1) (λ κ2x1 → κ2ac .fst .snd Y0 Y1 YY (k0 x0) κ2x1 × (κ2x1 ≡ h .morphism Y1 (k1 x1)))
          hypk-fwd = hypk x0 x1 xx in

    transport (cong (κ2ac .fst .snd Y0 Y1 YY (k0 x0)) (hypk-fwd .snd .snd)) (hypk-fwd .snd .fst)) ,
    cong (λ blank → κ2 .snd .snd X1 Y1 blank (h .morphism Y1 ∘ k1)) (hyp .snd .snd)  ∙  sym (h .morphismBind X1 Y1 κ1x1 k1))

  from-A-bdsc : κ2ac .fst .snd A A (Path A) ≡ κ2ac .fst .snd A A (Bridge A)
  from-A-bdsc = cong (κ2ac .fst .snd A A)
    (funExt λ a0 → funExt λ a1 → ua (isBDisc→equiv A isbdscA a0 a1))

  from-κ2-nrel : κ2ac .fst .snd A A (Bridge A) ≡ BridgeP (λ x → κ2 .fst A)
  from-κ2-nrel = outEquGrInv (κ2acnativrel A A (Bridge A) (λ _ → A) (inEquGrInv refl))

  from-κ2-bdsc : Bridge (κ2 .fst A) ≡ Path (κ2 .fst A)
  from-κ2-bdsc = funExt λ v0 → funExt λ v1 → sym (ua (isBDisc→equiv (κ2 .fst A) isbκ2A v0 v1))

  together : κ2ac .fst .snd A A (Path A) ≡ Path (κ2 .fst A)
  together = from-A-bdsc ∙ from-κ2-nrel ∙ from-κ2-bdsc

  eq : (x y : κ2 .fst A) →  κ2ac .fst .snd A A (Path A) x y ≡ Path (κ2 .fst A) x y 
  eq x y = cong (λ blank → blank y) (cong (λ blank → blank x) together)

  voigt-thm3 : ∀ (mas : List (κ1 .fst A)) → f  ((tt , κ2 .fst) , κ2 .snd .fst , κ2 .snd .snd) (map (h .morphism A) mas )  ≡ h .morphism A (f ((tt , κ1 .fst) , κ1 .snd .fst , κ1 .snd .snd) mas)
  voigt-thm3 mas =
    let partialParam = param premonRRG voigtdRRG f ((tt , κ2 .fst) , κ2 .snd .fst , κ2 .snd .snd) ((tt , κ1 .fst) , κ1 .snd .fst , κ1 .snd .snd) edge-κ2-κ1 (map (h .morphism A) mas) mas (aux mas) in   
       
    (transport (eq (f ((tt , κ2 .fst) , κ2 .snd .fst , κ2 .snd .snd) (map (h .morphism A) mas)) (partialParam .fst)) (partialParam .snd .fst)) ∙ partialParam .snd .snd  

      where

      aux : ∀ (mas : List (κ1 .fst A)) → ListRCover (edge-κ2-κ1 .fst .snd A A (Path A)) (map (h .morphism A) mas) mas
      aux [] = lift tt
      aux (ma ∷ mas) = (h .morphism A ma , transport (sym (eq (h .morphism A ma) (h .morphism A ma))) refl , refl) , aux mas

  voigt-thm4 : ∀ (mas1 mas2 : List (κ1 .fst A)) → map (h .morphism A) mas1 ≡ map (h .morphism A) mas2 → h .morphism A (f ((tt , κ1 .fst) , κ1 .snd .fst , κ1 .snd .snd) mas1) ≡ h .morphism A (f ((tt , κ1 .fst) , κ1 .snd .fst , κ1 .snd .snd) mas2)
  voigt-thm4 mas1 mas2 eq =  (sym (voigt-thm3 mas1)  ∙ cong (f ((tt , κ2 .fst) , κ2 .snd .fst , κ2 .snd .snd)) eq )  ∙ voigt-thm3 mas2
