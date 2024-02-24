{-# OPTIONS --type-in-type #-}
-- | Monoids on Poly
module Poly.Monoid where

--------------------------------------------------------------------------------

open import Poly

--------------------------------------------------------------------------------

-- | A monoid structure in Poly with no laws provided
record ProposedMonoid (_⊙_ : Poly → Poly → Poly) (I : Poly) : Set where
  field
    P : Poly
    e : I ⇒ P 
    _⋆_ : P ⊙ P ⇒ P
