{-# OPTIONS --type-in-type #-}
module Poly.Monoidal.Coproduct where

--------------------------------------------------------------------------------

open import Data.Product using (_,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit
open import Poly
open import Poly.Comonoid
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

+-split-l : ∀{P : Poly} → P ⇒ P + P
map-base +-split-l p-base = inj₁ p-base
map-fiber +-split-l p-base p-fib = p-fib

+-split-r : ∀{P : Poly} → P ⇒ P + P
map-base +-split-r p-base = inj₂ p-base
map-fiber +-split-r p-base p-fib = p-fib

+-monoid : ∀{P : Poly} → ProposedMonoid (_+_) 𝟘
ProposedMonoid.P (+-monoid {P}) = P
map-base (ε (+-monoid {P})) ()
map-fiber (ε (+-monoid {P})) () _
map-base (_⋆_ (+-monoid {P})) (inj₁ p-base) = p-base
map-base (_⋆_ (+-monoid {P})) (inj₂ p-base) = p-base
map-fiber (_⋆_ (+-monoid {P})) (inj₁ p-base) p-fib = p-fib
map-fiber (_⋆_ (+-monoid {P})) (inj₂ p-base) p-fib = p-fib

+-unital-r : ∀{P : Poly} → ProposedIso (P + 𝟘) P
map-base (fwd +-unital-r) (inj₁ p-base) = p-base
map-fiber (fwd +-unital-r) (inj₁ p-base) p-fib = p-fib
map-base (bwd +-unital-r) p-base = inj₁ p-base
map-fiber (bwd +-unital-r) p-base p-fib = p-fib

+-unital-l : ∀{P : Poly} → ProposedIso (𝟘 + P) P
map-base (fwd +-unital-l) (inj₂ p-base) = p-base
map-fiber (fwd +-unital-l) (inj₂ p-base) p-fib = p-fib
map-base (bwd +-unital-l) p-base = inj₂ p-base
map-fiber (bwd +-unital-l) p-base p-fib = p-fib

-- | Co-Product Left Inclusion
leftₚ : ∀{P Q : Poly} → P ⇒ (P + Q) 
leftₚ = +-unital-r .bwd ⨟ₚ idₚ +⇒ +-monoid .ε

-- | Co-Product Right Inclusion
rightₚ : ∀{P Q : Poly} → Q ⇒ (P + Q)
rightₚ = +-unital-l .bwd ⨟ₚ +-monoid .ε +⇒ idₚ

-- | Co-Product eliminator
eitherₚ : ∀{P Q R : Poly} → P ⇒ R → Q ⇒ R → (P + Q) ⇒ R
eitherₚ p⇒r q⇒r .map-base (inj₁ ptag) = p⇒r .map-base ptag
eitherₚ p⇒r q⇒r .map-base (inj₂ qtag) = q⇒r .map-base qtag
eitherₚ p⇒r q⇒r .map-fiber (inj₁ tag) = p⇒r .map-fiber tag
eitherₚ p⇒r q⇒r .map-fiber (inj₂ tag) = q⇒r .map-fiber tag

+-left : ∀{P Q R : Poly} → P ⇒ Q → (P + R) ⇒ (Q + R)
+-left p⇒q .map-base (inj₁ ptag) = inj₁ (map-base p⇒q ptag)
+-left p⇒q .map-base (inj₂ rtag) = inj₂ rtag
+-left p⇒q .map-fiber (inj₁ ptag) args = map-fiber p⇒q ptag args
+-left p⇒q .map-fiber (inj₂ rtag) args = args

right : ∀{P Q R : Poly} → P ⇒ Q → (R + P) ⇒ (R + Q)
right p⇒q .map-base (inj₁ rtag) = inj₁ rtag
right p⇒q .map-base (inj₂ ptag) = inj₂ (map-base p⇒q ptag)
right p⇒q .map-fiber (inj₁ rtag) args = args
right p⇒q .map-fiber (inj₂ ptag) args = map-fiber p⇒q ptag args

-- | Index sums
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
