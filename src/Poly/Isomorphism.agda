{-# OPTIONS --type-in-type #-}
-- | Isomorphisms in Poly
module Poly.Isomorphism where

--------------------------------------------------------------------------------

open import Poly

--------------------------------------------------------------------------------

-- | An Isomorphism in Poly with no laws provided
record ProposedIso (P Q : Poly) : Set where
  field
    fwd : P ⇒ Q
    bwd : Q ⇒ P

open ProposedIso public
