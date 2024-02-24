{-# OPTIONS --type-in-type #-}
-- | Comonoids on Poly
module Poly.Comonoid where

--------------------------------------------------------------------------------

open import Poly

--------------------------------------------------------------------------------

record ProposedComonoid (_⊙_ : Poly → Poly → Poly) (I : Poly) : Set where
  constructor proposedComonoid
  field
    P : Poly
    e : P ⇒ I 
    _⋆_ : P ⇒ P ⊙ P
