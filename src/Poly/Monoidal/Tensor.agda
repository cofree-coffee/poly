{-# OPTIONS --type-in-type #-}
module Poly.Monoidal.Tensor where

--------------------------------------------------------------------------------

open import Data.Product using (_×_; _,_)
open import Function using (id)
open import Poly
open import Poly.Monoid
open import Poly.SetFunctor

open _≃_

--------------------------------------------------------------------------------

-- | P ⊗ Q
-- Also called the Parallel Product of two Polynomials
--
-- P ⊗ Q ≔ ∑[ i ∈ P .Base × Q .Base ] y^(aᵢ × bⱼ)
infixr 7 _⊗_
_⊗_ : Poly → Poly → Poly
(P ⊗ Q) .Base  = Base P × Base Q
(P ⊗ Q) .Fiber (ptag , qtag) = Fiber P ptag × Fiber Q qtag

_⊗⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P ⊗ R ⇒ Q ⊗ Z
(p⇒q ⊗⇒ r⇒z) .map-base (ptag , rtag) = (map-base p⇒q ptag) , (map-base r⇒z rtag)
(p⇒q ⊗⇒ r⇒z) .map-fiber (ptag , rtag) (qargs , zargs) = (map-fiber p⇒q ptag qargs) , (map-fiber r⇒z rtag zargs)

-- ⊗-unit : ∀{P : Poly} → 𝕐 ⇒ P
-- ⊗-unit .map-base tt = {!!}
-- ⊗-unit .map-fiber tt pfib = tt

-- ⊗-merge : ∀{P : Poly} → P ⊗ P ⇒ P
-- ⊗-merge .map-base (pbase₁ , pbase₂) = {!!}
-- ⊗-merge .map-fiber (pbase₁ , pbase₂) pfib = {!!}

-- ⊗-monoid : ProposedMonoid (_⊗_) 𝕐
-- ⊗-monoid =
--   record
--     { e = ⊗-unit
--     ; _⋆_ = ⊗-merge
--     }

⊗-swap : ∀{P Q : Poly} → P ⊗ Q ⇒ Q ⊗ P
⊗-swap .map-base (ptag , qtag) = qtag , ptag
⊗-swap .map-fiber tag (qargs , pargs) = pargs , qargs

⊗-dupe : ∀{P : Poly} → P ⇒ P ⊗ P
⊗-dupe .map-base ptag =  ptag , ptag
⊗-dupe .map-fiber ptag (f , g) = f

-- | The parallel product represents day convolution.
⊗-⟦⟧ : ∀{P Q : Poly} → ⟦ P ⊗ Q ⟧ ≃ day ⟦ P ⟧ ⟦ Q ⟧
⊗-⟦⟧ {P = P} {Q = Q} .to ((ptag , qtag) , f) = P .Fiber ptag , Q .Fiber qtag , (λ pargs qargs → f (pargs , qargs)) , (ptag , id) , (qtag , id)
⊗-⟦⟧ .from (B , C , f , (ptag , b) , (qtag , c)) = (ptag , qtag) , λ (pargs , qargs) → f (b pargs) (c qargs)
