{-# OPTIONS --type-in-type #-}
module Poly.Monoidal.Coproduct where

--------------------------------------------------------------------------------

open import Data.Product using (_,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Poly
open import Poly.Monoid
open import Poly.Isomorphism
open import Poly.SetFunctor

open ProposedIso
open _≃_

--------------------------------------------------------------------------------

-- | P + Q
-- The Categorical Co-Product of two Polyonomials
--
-- P + Q ≔ ∑[ j ∈ I ] x^aᵢ + ∑[ j ∈ J ] y^bⱼ
infixr 6 _+_
_+_ : Poly → Poly → Poly
(P + Q) .Base = P .Base ⊎ Q .Base
(P + Q) .Fiber (inj₁ x) = P .Fiber x
(P + Q) .Fiber (inj₂ y) = Q .Fiber y

_+⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P + R ⇒ Q + Z
(p⇒q +⇒ r⇒z) .map-base (inj₁ ptag) = inj₁ (map-base p⇒q ptag)
(p⇒q +⇒ r⇒z) .map-base (inj₂ rtag) = inj₂ (map-base r⇒z rtag)
(p⇒q +⇒ r⇒z) .map-fiber (inj₁ ptag) = map-fiber p⇒q ptag
(p⇒q +⇒ r⇒z) .map-fiber (inj₂ rtag) = map-fiber r⇒z rtag

+-unit : ∀{p : Poly} → 𝟘 ⇒ p
+-unit .map-base ()
+-unit .map-fiber () _

+-merge : ∀{P : Poly} → P + P ⇒ P
+-merge .map-base (inj₁ ptag) = ptag
+-merge .map-base (inj₂ ptag) = ptag
+-merge .map-fiber (inj₁ ptag) pargs = pargs
+-merge .map-fiber (inj₂ ptag) pargs = pargs

+-monoid : ∀{P : Poly} → ProposedMonoid (_+_) 𝟘
+-monoid {P} =
  record
    { P = P
    ; e = +-unit
    ; _⋆_ = +-merge
    }

+-unital-r-fwd : ∀{P : Poly} → P + 𝟘 ⇒ P
+-unital-r-fwd .map-base (inj₁ pbase) = pbase
+-unital-r-fwd .map-fiber (inj₁ x) pfib = pfib

+-unital-r-bwd : ∀{P : Poly} → P ⇒ P + 𝟘
+-unital-r-bwd .map-base pbase = inj₁ pbase
+-unital-r-bwd .map-fiber pbase pfib = pfib

+-unital-r : ∀{P : Poly} → ProposedIso (P + 𝟘) P
+-unital-r =
  record
    { fwd = +-unital-r-fwd
    ; bwd = +-unital-r-bwd
    }

+-unital-l-fwd : ∀{p : Poly} → 𝟘 + p ⇒ p
+-unital-l-fwd .map-base (inj₂ pbase) = pbase
+-unital-l-fwd .map-fiber (inj₂ x) pfib = pfib

+-unital-l-bwd : ∀{p : Poly} → p ⇒ 𝟘 + p
+-unital-l-bwd .map-base pbase = inj₂ pbase
+-unital-l-bwd .map-fiber pbase pfib = pfib

+-unital-l : ∀{P : Poly} → ProposedIso (𝟘 + P) P
+-unital-l =
  record
    { fwd = +-unital-l-fwd
    ; bwd = +-unital-l-bwd
    }

-- | Co-Product Left Inclusion
leftₚ : ∀{P Q : Poly} → P ⇒ (P + Q) 
leftₚ = +-unital-r .bwd ⨟ₚ idₚ +⇒ +-unit

-- | Co-Product Right Inclusion
rightₚ : ∀{P Q : Poly} → Q ⇒ (P + Q)
rightₚ = +-unital-l .bwd ⨟ₚ +-unit +⇒ idₚ

-- | Co-Product eliminator
eitherₚ : ∀{P Q R : Poly} → P ⇒ R → Q ⇒ R → (P + Q) ⇒ R
eitherₚ p⇒r q⇒r .map-base (inj₁ ptag) = p⇒r .map-base ptag
eitherₚ p⇒r q⇒r .map-base (inj₂ qtag) = q⇒r .map-base qtag
eitherₚ p⇒r q⇒r .map-fiber (inj₁ tag) = p⇒r .map-fiber tag
eitherₚ p⇒r q⇒r .map-fiber (inj₂ tag) = q⇒r .map-fiber tag

Sum : (I : Set) → (I → Poly) → Poly
Sum I P .Base = ∃[ i ] P i .Base
Sum I P .Fiber (i , ptag) = P i .Fiber ptag

infix 2 Sum
syntax Sum I (λ i → P) = Σₚ[ i ∈ I ] P

⟦⟧-+ : ∀{P Q : Poly} → ⟦ P + Q ⟧ ≃ ⟦ P ⟧ +₁ ⟦ Q ⟧
⟦⟧-+ .to (inj₁ ptag , x) = inj₁ (ptag , x)
⟦⟧-+ .to (inj₂ qtag , y) = inj₂ (qtag , y)
⟦⟧-+ .from (inj₁ (ptag , x)) = inj₁ ptag , x
⟦⟧-+ .from (inj₂ (qtag , y)) = inj₂ qtag , y

⟦⟧-Sum : {I : Set} → {P : I → Poly} → ⟦ Σₚ[ i ∈ I ] (P i) ⟧ ≃ (Σ₁[ i ∈ I ] ⟦ P i ⟧)
⟦⟧-Sum .to ((i , ptag) , f) = i , ptag , f
⟦⟧-Sum .from (i , ptag , f) = (i , ptag) , f
