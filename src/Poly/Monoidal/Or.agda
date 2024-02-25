{-# OPTIONS --type-in-type #-}
module Poly.Monoidal.Or where

--------------------------------------------------------------------------------

open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id)
open import Poly
open import Poly.Monoidal.Coproduct
open import Poly.Monoidal.Product


--------------------------------------------------------------------------------

-- | P ∨ Q
--
-- P ∨ Q ≔ P + (P ⊗ Q) + Q
infixr 5 _∨_
_∨_ :  Poly → Poly → Poly
P ∨ Q = P + (P ×ₚ Q) + Q

-- _∨⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P ∨ R ⇒ Q ∨ Z
-- (p⇒q ∨⇒ r⇒z) .map-base (inj₁ ptag) = inj₁ (map-base p⇒q ptag)
-- (p⇒q ∨⇒ r⇒z) .map-base (inj₂ (inj₁ (ptag , rtag))) = inj₂ (inj₁ ((map-base p⇒q ptag) , (map-base r⇒z rtag)))
-- (p⇒q ∨⇒ r⇒z) .map-base (inj₂ (inj₂ rtag)) = inj₂ (inj₂ (map-base r⇒z rtag))
-- (p⇒q ∨⇒ r⇒z) .map-fiber (inj₁ ptag) args = map-fiber p⇒q ptag args
-- (p⇒q ∨⇒ r⇒z) .map-fiber (inj₂ (inj₁ (ptag , rtag))) (qargs , zargs) = (map-fiber p⇒q ptag qargs) , map-fiber r⇒z rtag zargs
-- (p⇒q ∨⇒ r⇒z) .map-fiber (inj₂ (inj₂ rtag)) args = map-fiber r⇒z rtag args

-- | _∨_ This Inclusion
This : ∀{P Q : Poly} → P ⇒ (P ∨ Q)
This .map-base ptag = inj₁ ptag
This .map-fiber ptag = id

-- | _∨_ That Inclusion
That : ∀{P Q : Poly} → Q ⇒ (P ∨ Q)
That .map-base qtag = inj₂ (inj₂ qtag)
That .map-fiber qtag = id

-- | _∨_ These Inclusion
These : ∀{P Q : Poly} → (P ×ₚ Q) ⇒ (P ∨ Q)
These .map-base tags = inj₂ (inj₁ tags)
These .map-fiber tags = id

-- | _∨_ Eliminator
theseₚ : ∀{P Q R : Poly} → P ⇒ R → Q ⇒ R → (P ×ₚ Q) ⇒ R → (P ∨ Q) ⇒ R
(theseₚ p⇒r q⇒r pq⇒r) .map-base  (inj₁ ptag) = map-base p⇒r ptag
(theseₚ p⇒r q⇒r pq⇒r) .map-base (inj₂ (inj₁ tags)) = map-base pq⇒r tags
(theseₚ p⇒r q⇒r pq⇒r) .map-base (inj₂ (inj₂ qtag)) = map-base q⇒r qtag
(theseₚ p⇒r q⇒r pq⇒r) .map-fiber (inj₁ ptag) args = map-fiber p⇒r ptag args
(theseₚ p⇒r q⇒r pq⇒r) .map-fiber (inj₂ (inj₁ tags)) args = map-fiber pq⇒r tags args
(theseₚ p⇒r q⇒r pq⇒r) .map-fiber (inj₂ (inj₂ qtag)) args = map-fiber q⇒r qtag args
--theseₚ p⇒r q⇒r pq⇒r = {!!}
