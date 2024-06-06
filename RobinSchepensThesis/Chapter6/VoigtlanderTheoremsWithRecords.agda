{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module VoigtlanderTheoremsWithRecords where

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


postulate
  l : Level
  A : Type l --in fine, bridge discreteness is needed for A (it is somehow implied by asking dnativh,
  isbA : isBDisc A 

--simplified bare param for theorem 3

bare-param :  (f : Type l → Type l) (aa : Bridge (Type l) A A) → Bridge (Type l) (f A) (f A)
bare-param f aa = λ x → f(aa x)



-- type of premonads

record PMnd : Type (ℓ-suc l) where
  field
    pmnd : Type l → Type l
    ret : ∀ (X : Type l) → X → pmnd X
    bind : ∀ (X Y : Type l) → pmnd X → (X → pmnd Y) → pmnd Y
open PMnd public


--id is a premonad

IdPmnd : PMnd
IdPmnd =
  record {
    pmnd = λ X → X ;
    ret = λ X x → x ;
    bind = λ X Y κx k → k κx
  }

--PreMonad morphism

record PMndMorphism (κ0 κ1 : PMnd) : Type (ℓ-suc l) where
  field
    morphism : (X : Type l) → κ0 .pmnd X → κ1 .pmnd X 
    morphismRet : (X : Type l) (x : X) → morphism X (κ0 .ret X x) ≡ κ1 .ret X x  
    morphismBind :  (X Y : Type l) (κx0 : κ0 .pmnd X) (k : X → κ0 .pmnd Y) → morphism Y (κ0 .bind X Y κx0 k) ≡ κ1 .bind X Y (morphism X κx0) ((morphism Y) ∘ k)
open PMndMorphism public    

-- postulating the RRG and dRRGs

record PMndEdge (M0 M1 : PMnd) : Type (ℓ-suc l) where
  field
    relac : ∀ X0 X1 → (X0 → X1 → Type l) → (M0 .pmnd X0 → M1 .pmnd X1 → Type l)
    retRel : ∀ X0 X1 (XX : X0 → X1 → Type l) (x0 : X0) (x1 : X1) (xx : XX x0 x1) →
      relac X0 X1 XX (M0 .ret X0 x0) (M1 .ret X1 x1)
    bindRel : ∀ (X0 X1 : Type l) (XX : X0 → X1 → Type l)
      (Y0 Y1 : Type l) (YY : Y0 → Y1 → Type l) →
      (m0 : M0 .pmnd X0) (m1 : M1 .pmnd X1) (mm : relac X0 X1 XX m0 m1) →
      (k0 : X0 → M0 .pmnd Y0) (k1 : X1 → M1 .pmnd Y1) (kk : ∀ x0 x1 (xx : XX x0 x1) → relac Y0 Y1 YY (k0 x0) (k1 x1)) →
      relac Y0 Y1 YY (M0 .bind X0 Y0 m0 k0) (M1 .bind X1 Y1 m1 k1)
open PMndEdge public

NativH = (M0 M1 : PMnd) → (PMndEdge M0 M1) ≃ (Bridge (PMnd) M0 M1)

postulate
  nath : NativH


PMndNRG :  NRGraph (ℓ-suc l)
PMndNRG  =
  record {
    nrg-cr = PMnd  ;
    nedge = PMndEdge ;
    nativ = nath
  }

voigt : ∀ (M : PMnd) → Type l
voigt M = List (M .pmnd A) → M .pmnd A

voigtDedge : (M0 M1 : PMnd) (MM : PMndEdge M0 M1) (v0 : voigt M0) (v1 : voigt M1) → Type l
voigtDedge M0 M1 MM v0 v1 =
  ∀ (mas0 : List (M0 .pmnd A)) (mas1 : List (M1 .pmnd A)) (mass : ListRCover (MM .relac A A (Path A))  mas0 mas1) →
  MM .relac A A (Path A)  (v0 mas0) (v1 mas1)



DNativH =
  ∀ M0 M1 MM (Mbdg : Bridge PMnd M0 M1) (Mprf : _[_]_ MM (nath _ _) Mbdg) v0 v1 →
    (voigtDedge M0 M1 MM v0 v1) ≃ BridgeP (λ x → voigt (Mbdg x)) v0 v1

postulate
  dnativh : DNativH

voigtDNRG :  DispNRG l PMndNRG
voigtDNRG = record {
  dcr = voigt ;
  dedge = voigtDedge ;
  dnativ = dnativh }
  

--postulating second dRRG for theorem 5

voigt2 : ∀ (κ : PMnd) → Type (ℓ-suc l)
voigt2 κ = (X : Type l) → List (κ .pmnd X) → κ .pmnd (List X)

voigt2Dedge : (κ1 κ2 : PMnd) (κκ : PMndEdge κ1 κ2) (v1 : voigt2 κ1) (v2 : voigt2 κ2) → Type (ℓ-suc l)
voigt2Dedge κ1 κ2 κκ v1 v2 =
    ∀ (X0 X1 : Type l) (XX : X0 → X1 → Type l) (mas1 : List (κ1 .pmnd X0)) (mas2 : List (κ2 .pmnd X1)) (mass : ListRCover (κκ .relac X0 X1 (XX)) mas1 mas2) →
  κκ .relac (List X0) (List X1) (ListRCover XX) (v1 X0  mas1) (v2 X1 mas2)

Voigt2Nativ = ∀ κ1 κ2 κκ (κbdg : Bridge PMnd κ1 κ2) (κprf : _[_]_ κκ (nath _ _) κbdg) v1 v2 → (voigt2Dedge κ1 κ2 κκ v1 v2) ≃ BridgeP (λ x → voigt2 (κbdg x)) v1 v2

postulate
  voigt2nativ : Voigt2Nativ
  
voigtDNRG2 : DispNRG (ℓ-suc l) PMndNRG
voigtDNRG2 = record {
  dcr = voigt2 ;
  dedge = voigt2Dedge ;
  dnativ = voigt2nativ }


module VOIGT1
  (f : (κ : PMnd) → List (κ .pmnd A) → κ .pmnd A)
  (κ : PMnd)
  (law1-κ : (X Y : Type l) (x : X) (k : X → κ .pmnd Y) → (κ .bind X Y (κ .ret X x) k) ≡ k x)
  where

  pureval : κ .pmnd A → Type l
  pureval κa = Σ A (λ a → κa ≡ κ .ret A a)

  purelist : List (κ .pmnd A) → Type l
  purelist [] = Lift Unit
  purelist (ma ∷ mas) = pureval ma × (purelist mas)

  giveVals : (mas : List (κ .pmnd A)) (plis : purelist mas) → List A
  giveVals [] plis = []
  giveVals (ma ∷ mas) (pma , pmas) = (pma .fst) ∷ giveVals mas pmas 

  edge-κ-Id : PMndEdge κ IdPmnd
  edge-κ-Id =
    record {
      relac = λ X0 X1 XX κx0 x1 → Σ X0 (λ x0 → (κ .ret X0 x0 ≡ κx0) × (XX x0 x1)) ;
      retRel = λ X0 X1 XX x0 x1 xx → x0 , refl , xx  ;
      bindRel = λ X0 X1 XX Y0 Y1 YY κx0 x1 hyp k0 k1 hypk →
        let
        
          dedct1 : κ .ret X0 (hyp .fst) ≡ κx0
          dedct1 = hyp .snd .fst

         
          hypk-fwd : Σ Y0 (λ y0 → (κ .ret Y0 y0 ≡ k0 (hyp .fst)) × YY y0 (k1 x1))
          hypk-fwd  = hypk (hyp .fst) x1 (hyp .snd .snd) in
          
        hypk-fwd .fst ,
        ((hypk-fwd .snd .fst) ∙ (sym (law1-κ X0 Y0 (hyp .fst) k0)))
        ∙ cong (λ blank → κ .bind X0 Y0 blank k0) dedct1  ,
        hypk-fwd .snd .snd
        
    }
    
  voigt-thm1 : ∀ (mas : List (κ .pmnd A)) →
    purelist mas → pureval (f κ mas)
  voigt-thm1 mas plis =
    let
      partialParam = param PMndNRG voigtDNRG f κ IdPmnd edge-κ-Id mas (giveVals mas plis) (aux mas plis)
    in
    partialParam .fst ,  sym (partialParam .snd .fst) 

    where

      aux : ∀ mas plis →
       ListRCover
       (λ κa a1 → Σ A (λ a0 → (κ .ret A a0 ≡ κa) × Path A a0 a1)) mas
       (giveVals mas plis)
      aux [] _ = lift tt
      aux (ma ∷ mas) (pma , pmas) =
        (pma .fst , (sym (pma .snd)) , refl) ,
        aux mas pmas

module VOIGT2
  (f : ∀ (M : PMnd ) → voigt M)
  (κ : PMnd)
  (p : ∀ (A : Type l) → κ .pmnd A → A)
  (eq1 : ∀ (X : Type l) (x : X) → (p X (κ .ret X x)) ≡ x)
  (eq2 : ∀ (X : Type l) (Y : Type l) (κx : κ .pmnd X) (q : X → κ .pmnd Y) → p Y (κ .bind X Y κx q) ≡ p Y (q (p X  κx)))
  where

  
  edge : PMndEdge κ IdPmnd
  edge = record {
      relac = λ X0 X1 XX κx0 x1 → Σ X0 (λ x0 → (p X0 κx0 ≡ x0) × (XX x0 x1)) ;
      retRel = λ X0 X1 XX x0 x1 xx → x0 , eq1 X0 x0 , xx ;
      bindRel = λ X0 X1 XX Y0 Y1 YY κx0 x1 hyp k0 k1 hypk →
      
        let hypk-fwd : Σ Y0 (λ y0 → (p Y0 (k0 (hyp .fst)) ≡ y0) × YY y0 (k1 x1))
            hypk-fwd = hypk (hyp .fst) (x1) (hyp .snd .snd)

            dedct1 : p X0 κx0 ≡ hyp .fst
            dedct1 = hyp .snd .fst

            apEq2 : p Y0 (κ .bind X0 Y0 κx0 k0) ≡ p Y0 (k0 (p X0 κx0))
            apEq2 = eq2 X0 Y0 κx0 k0 in


        hypk-fwd .fst ,
        sym (sym (cong (p Y0) (cong k0 dedct1) ∙ hypk-fwd .snd .fst) ∙ sym apEq2) ,
        hypk-fwd .snd .snd }

        
  voigt-thm2 : ∀ (mas : List (κ .pmnd A)) → p A (f κ mas) ≡ f IdPmnd (map (p A) mas)
  voigt-thm2 mas = 
    let
      partialParam = param PMndNRG voigtDNRG f κ IdPmnd edge mas (map (p A) mas) (aux mas) in
    partialParam .snd .fst ∙ partialParam .snd .snd

    where

      aux : ∀ (mas : List (κ .pmnd A)) → ListRCover (λ κa a1 → Σ A (λ a0 → (p A κa ≡ a0) × Path A a0 a1)) mas (map (p A) mas)
      aux [] = lift tt
      aux (ma ∷ mas) = (p A ma , refl , refl) , aux mas


module VOIGT3
  (f : (κ : PMnd) → List (κ .pmnd A) → κ .pmnd A)
  (κ1 κ2 : PMnd) 
  (h : PMndMorphism κ1 κ2)
  where
    
  κ2ac : PMndEdge κ2 κ2
  κ2ac  = invEq (nath κ2 κ2) (λ x → κ2)

  κ2acNativRel = (g0 g1 : Type l) (gg : (TypeNRG l) .nedge g0 g1) (gbdg : BridgeP (λ _ → Type l) g0 g1) → gg [ relativity ] gbdg → κ2ac .relac g0 g1 gg [ relativity ] (λ x → κ2 .pmnd (gbdg x))

  postulate
    κ2acnativrel : κ2acNativRel
    isbdscA : isBDisc A
    isbκ2A : isBDisc (κ2 .pmnd A)

  

  κ2asNRelator : NRelator (TypeNRG l) (TypeNRG l)
  κ2asNRelator = record {
    nrel0 = κ2 .pmnd ;
    nrel1 = κ2ac .relac ;
    nativ-rel = κ2acnativrel }

 
  from-A-bdsc : κ2ac .relac A A (Path A) ≡ κ2ac .relac A A (Bridge A)
  from-A-bdsc = cong (κ2ac .relac A A)
    (funExt λ a0 → funExt λ a1 → ua (isBDisc→equiv A isbdscA a0 a1))

  from-κ2-nrel : κ2ac .relac A A (Bridge A) ≡ BridgeP (λ x → κ2 .pmnd A)
  from-κ2-nrel = outEquGrInv (κ2acnativrel A A (Bridge A) (λ _ → A) (inEquGrInv refl))

  from-κ2-bdsc : Bridge (κ2 .pmnd A) ≡ Path (κ2 .pmnd A)
  from-κ2-bdsc = funExt λ v0 → funExt λ v1 → sym (ua (isBDisc→equiv (κ2 .pmnd A) isbκ2A v0 v1))

  together : κ2ac .relac A A (Path A) ≡ Path (κ2 .pmnd A)
  together = from-A-bdsc ∙ from-κ2-nrel ∙ from-κ2-bdsc

  eq : (x y : κ2 .pmnd A) →  κ2ac .relac A A (Path A) x y ≡ Path (κ2 .pmnd A) x y 
  eq x y = cong (λ blank → blank y) (cong (λ blank → blank x) together)


  edge-κ2-κ1 : PMndEdge κ2 κ1
  edge-κ2-κ1 = record {
    relac = λ X0 X1 XX κ2x0 κ1x1 → Σ (κ2 .pmnd X1) (λ κ2x1 → (κ2ac .relac X0 X1 XX κ2x0 κ2x1) × (κ2x1 ≡ h .morphism X1 κ1x1)) ;
    retRel = λ X0 X1 XX x0 x1 xx → κ2 .ret X1 x1 , κ2ac .retRel X0 X1 XX x0 x1 xx , sym (h .morphismRet X1 x1) ;
    bindRel = λ X0 X1 XX Y0 Y1 YY κ2x0 κ1x1 hyp k0 k1 hypk → κ2 .bind X1 Y1 (hyp .fst) (λ x1 → h .morphism Y1 (k1 x1)) ,
    κ2ac .bindRel X0 X1 XX Y0 Y1 YY κ2x0 (hyp .fst) (hyp .snd .fst) k0 (λ x1 → h .morphism Y1 (k1 x1))
      (λ x0 x1 xx →

      let hypk-fwd = Σ (κ2 .pmnd Y1) (λ κ2x1 → κ2ac .relac Y0 Y1 YY (k0 x0) κ2x1 × (κ2x1 ≡ h .morphism Y1 (k1 x1)))
          hypk-fwd = hypk x0 x1 xx in

    transport (cong (κ2ac .relac Y0 Y1 YY (k0 x0)) (hypk-fwd .snd .snd)) (hypk-fwd .snd .fst)) ,
    cong (λ blank → κ2 .bind X1 Y1 blank (h .morphism Y1 ∘ k1)) (hyp .snd .snd)  ∙  sym (h .morphismBind X1 Y1 κ1x1 k1) }


  voigt-thm3 : ∀ (mas : List (κ1 .pmnd A)) → f κ2 (map (h .morphism A) mas )  ≡ h .morphism A (f κ1 mas)
  voigt-thm3 mas =
    let partialParam = param PMndNRG voigtDNRG f κ2 κ1 edge-κ2-κ1 (map (h .morphism A) mas) mas (aux mas) in   
       
    (transport (eq (f κ2 (map (h .morphism A) mas)) (partialParam .fst)) (partialParam .snd .fst)) ∙ partialParam .snd .snd  

      where

      aux : ∀ (mas : List (κ1 .pmnd A)) → ListRCover (edge-κ2-κ1 .relac A A (Path A)) (map (h .morphism A) mas) mas
      aux [] = lift tt
      aux (ma ∷ mas) = (h .morphism A ma , transport (sym (eq (h .morphism A ma) (h .morphism A ma))) refl , refl) , aux mas

  
  voigt-thm4 : ∀ (mas1 mas2 : List (κ1 .pmnd A)) → map (h .morphism A) mas1 ≡ map (h .morphism A) mas2 → h .morphism A (f κ1 mas1) ≡ h .morphism A (f κ1 mas2)
  voigt-thm4 mas1 mas2 eq =  (sym (voigt-thm3 mas1)  ∙ cong (f κ2) eq )  ∙ voigt-thm3 mas2
