{-# OPTIONS --type-in-type #-}
module Poly.Types.Lott where


--------------------------------------------------------------------------------

open import Poly

--------------------------------------------------------------------------------
-- Δ : ℕ → 

lott : Poly
lott .Base = ℕ
lott .Fiber n = Σ[ p ∈ Δ n ] jj
