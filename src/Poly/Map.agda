{-# OPTIONS --type-in-type --allow-unsolved-metas #-}
module Poly.Map where

--------------------------------------------------------------------------------

import Data.Bool as B
open import Data.Bool hiding (T)
open import Data.Empty
open import Data.Fin
open import Data.Maybe
open import Data.Product 
open import Data.Sum
open import Data.Unit
open import Poly
open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------

private variable
  A B C D S T I O K V : Set
  P Q R : Poly

--------------------------------------------------------------------------------

Mapₚ : (K : Set) → Poly
(Mapₚ K) .Tag = K → Bool
Mapₚ K .Args = λ k→bool →  Σ[ k ∈ K ] B.T (k→bool k)

Map : (K : Set) → (V : Set) → Set
Map K V = ⟦ Mapₚ K ⟧ V

lookup : Map K V → K → Maybe V 
lookup (k→Bool , getter) k with k→Bool k in eq
... | false = nothing
... | true = just (getter (k , subst B.T (sym eq) tt))

insert : (K → K → Bool) → K → V → Map K V → Map K V
insert _≗_ k v (k→Bool , getter) = (λ k₁ → (k ≗ k₁) ∨ k→Bool k₁) , λ where
  (k , prf) → {!!}
