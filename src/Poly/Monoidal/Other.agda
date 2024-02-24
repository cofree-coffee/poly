{-# OPTIONS --type-in-type #-}
-- | Other Monoidal Structures on Poly
module Poly.Monoidal.Other where

--------------------------------------------------------------------------------

open import Data.Unit
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Poly
open import Poly.Comonoid
open import Poly.Monoid
open import Poly.Monoidal.Coproduct
open import Poly.Monoidal.Compose
open import Poly.Monoidal.Product
open import Poly.Monoidal.Tensor
open import Poly.Monoidal.Or

--------------------------------------------------------------------------------

-- | P Ⓥ Q
--
-- Σ[ (i , j) ∈ P .Base × Q . Base] x^(aᵢ Ⓥ bⱼ)
infixr 8 _Ⓥ_
_Ⓥ_ : Poly → Poly → Poly
(P Ⓥ Q) .Base = P .Base × Q .Base
(P Ⓥ Q) .Fiber = λ where
  (ptag , qtag) →  Fiber P ptag ⊎ (Fiber P ptag × Fiber Q qtag) ⊎ Fiber Q qtag

_Ⓥ⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P Ⓥ  R ⇒ Q Ⓥ Z
(p⇒q Ⓥ⇒ r⇒z) .map-base (ptag , rtag) = map-base p⇒q ptag , map-base r⇒z rtag
(p⇒q Ⓥ⇒ r⇒z) .map-fiber (ptag , rtag) (inj₁ qargs) = inj₁ (map-fiber p⇒q ptag qargs)
(p⇒q Ⓥ⇒ r⇒z) .map-fiber (ptag , rtag) (inj₂ (inj₁ (qargs , zargs))) = inj₂ (inj₁ ((map-fiber p⇒q ptag qargs) , (map-fiber r⇒z rtag zargs)))
(p⇒q Ⓥ⇒ r⇒z) .map-fiber (ptag , rtag) (inj₂ (inj₂ zargs)) = inj₂ (inj₂ (map-fiber r⇒z rtag zargs))

--------------------------------------------------------------------------------

-- | P ⊘ Q
--
-- P ⊘ Q ≔ P + (P ×ₚ Q) + Q
infixr 4 _⊘_
_⊘_ : Poly → Poly → Poly
P ⊘ Q = P + (P ×ₚ Q) + Q

--------------------------------------------------------------------------------

-- | P ⊛ Q
--
-- P ⊛ Q ≔  P + (P Ⓥ Q) + Q
infixr 4 _⊛_
_⊛_ : Poly → Poly → Poly
P ⊛ Q = P + (P Ⓥ Q) + Q

--------------------------------------------------------------------------------
-- For any symmetric monoidal product (I , _∙_) on Set, there is a corresponding
-- symmetric monoidal structure (y^I , ⊙) on Poly, where the monoidal product
-- given as:
--
--    Σ[ (p, q) ∈ P .Base × Q .Base ] (P .Fiber q) ∙ (Q .Fiber q)
--
-- TODO: Demand an actual monoid on set:
_⊙_ : (Set → Set → Set) → Poly → Poly → Poly
Base ((_∙_ ⊙ P) Q) = P .Base × Q .Base
Fiber ((_∙_ ⊙ P) Q) (p-base , q-base) = P .Fiber  p-base ∙ Q .Fiber  q-base
