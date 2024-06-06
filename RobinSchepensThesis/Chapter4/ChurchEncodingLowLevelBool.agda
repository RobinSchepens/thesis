{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module ChurchEncodingLowLevelBool where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.ExtentExamples
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool

-- Want to prove Bool ≃ (X : Type) → X → X → X (CH theorem 3.1)
-- Use isoToEquiv Lemma to prove equivalence, need : f : A → B , g = B → A , g ∘ f ≡ id , f ∘ g ≡ id

 -- true = projection on first component , false = projection on second component
leftToRight : Bool → (∀ (X : Type) → X → X → X)
leftToRight true = λ X → λ t → λ f → t
leftToRight false = λ X → λ t → λ f → f
  
-- Only feasible inverse
rightToLeft : (∀ (X : Type) → X → X → X) → Bool
rightToLeft k = k Bool true false


--Need to prove leftToRight (righToLeft k) A t f ≡ k A t f, use parametricity  
module ParametricityBool (k : ∀ (X : Type) → X → X → X) (A : Type) (t f : A) where

  --Define relation at universe type, note that t and true, f and false are related by R
  --(refl : R true t and refl : R false f)

  R : Bool → A → Type
  R b a = leftToRight b A t f ≡ a -- relation is graph of λ b. leftToRight b A t f

  --primGel : (A0 A1 : Type) (R : A0 → A1 → Type) (@tick x : BI) → Type using A0 = Bool, A1 = A,
  --R = see above (Gel Form rule). So we can apply k at primGel Bool A R x to obtain something of 
  -- type  primGel → primGel → primGel 
  --Always possible to abstract x : BI (see inference rules p16)

  kGelx : (@tick x : BI) → primGel Bool A R x → primGel Bool A R x → primGel Bool A R x
  kGelx = λ x → k (primGel Bool A R x)

  --prim^gel : {A0 A1 : Type} {R : A0 → A1 → Type} (M0 : A0) (M1 : A1) (P : R M0 M1) (@tick x : BI)
  -- → primGel A0 A1 R x using A0, A1, R as above (Gel Intro rule)
  -- first gel term: true : Bool , t : A , refl : R true t
  -- second gel term: false : Bool , f : A , refl : R false f

  kGelx-gel-gel : (@tick x : BI) → primGel Bool A R x
  kGelx-gel-gel = λ x → kGelx x (prim^gel true t refl x) (prim^gel false f refl x)

  --Now we can construct a bridge (using Bdg Intro rule) at primGel Bool A R x by using as function
  --kGelx-gel-gel. To check endpoints use Gel ∂ and gel ∂ rule. Gel ∂ at bi0: primGel Bool A R bi0
  -- → Bool, at bi1: primGel Bool A R bi1 → A    
  -- gel ∂ at bi0: prim^gel true t refl biO → true,
  -- prim^gel false f refl bi0 → false, at bi1: prim^gel true t refl bi1 → t and 
  -- prim^gel false f refl bi1 → f
  -- this leaves us with endpoints k Bool true false and k A t f 

  asBridge : BridgeP (λ x → primGel Bool A R x) (k Bool true false) (k A t f)
  asBridge = λ x → kGelx-gel-gel x

  -- Now we want to conclude that R (k Bool true false) (k A t f), we use prim^ungel :
  --{A0 A1 : Type} {R : A0 → A1 → Type} (absQ : (@tick x : BI) → primGel A0 A1 R x)
  --→ R (absQ bi0) (absQ bi1)

  ungel : R (k Bool true false) (k A t f)
  ungel = prim^ungel λ x → asBridge x

  -- Unwinding R (k Bool true false) (k A t f) gives leftToRight (k Bool true false) A t f ≡ k A t f
  -- Note that rightToLeft k = k Bool true false, so leftToRight (rightToLeft k) = k A t f,
  -- as desired

open ParametricityBool public
  
--Just unwind defintion and use refl
retract' : ∀ (b : Bool) → rightToLeft (leftToRight b) ≡ b
retract' true = refl
retract' false = refl

section' : ∀ (k : (∀ (X : Type) → X → X → X)) → leftToRight (rightToLeft k) ≡ k
section' = λ k → funExt λ A → funExt λ t → funExt λ f → ungel k A t f

boolIsoChurch : Bool ≃ ∀ (X : Type) → X → X → X
boolIsoChurch = isoToEquiv (iso leftToRight rightToLeft section' retract')
