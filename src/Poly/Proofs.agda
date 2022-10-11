{-# OPTIONS --type-in-type #-}
-- | TODO: Proofs
module Poly.Proofs where

--------------------------------------------------------------------------------

open import Function
open import Poly
open import Data.Product
open import Data.Fin
open import Data.Unit
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

--------------------------------------------------------------------------------

private variable
  A B C D S T I O : Set
  P Q R : Poly

--------------------------------------------------------------------------------
-- Poly Interpretation

-- ⟦P⟧⊤≅P-Tag : ⟦ P ⟧ ⊤ ≅ P .Tag
-- ⟦P⟧⊤≅P-Tag = ?

--------------------------------------------------------------------------------
-- Functor Laws

-- mapₚ-id : mapₚ id ⟦ P ⟧ A ≡ ⟦ P ⟧ A
-- mapₚ-id = ?

-- mapₚ-∘ₚ : (f : B → C) → (g : A → B) → mapₚ f ∘ mapₚ ≡ mapₚ (f ∘ g)
-- mapₚ-∘ₚ = ?

--------------------------------------------------------------------------------
-- Natural Transformations

-- ⇒-commutes : 

--------------------------------------------------------------------------------
-- Symmetric Monoidal Products

-- | ×ₚ distributes over +
-- p ×ₚ (q₁ + q₂) ≅ (p ×ₚ q₁) + (p ×ₚ q₂)
-- ×-distributes-+ = {!!}

-- | ⊗ distributes over +
-- p ⊗ (q₁ + q₂) ≅ (p ⊗ q₁) + (p ⊗ q₂)
-- ⊗-distributes-+ = {!!}

-- | ∨ distributes over +
-- p ∨ (q₁ + q₂) ≅ (p ∨ q₁) + (p ∨ q₂)
-- ∨-distributes-+ = {!!}

