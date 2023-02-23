{-# OPTIONS --type-in-type --allow-unsolved-metas #-}
module Poly.Map where

--------------------------------------------------------------------------------

open import Data.Bool using (_∨_; Bool; true; false; T)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Unit using (tt)
open import Poly
open import Relation.Binary.PropositionalEquality using (subst; sym)

--------------------------------------------------------------------------------

private variable
  A B C D S I O K V : Set
  P Q R : Poly

--------------------------------------------------------------------------------

Mapₚ : (K : Set) → Poly
(Mapₚ K) .Tag = K → Bool
Mapₚ K .Args = λ k→bool →  Σ[ k ∈ K ] T (k→bool k)

Map : (K : Set) → (V : Set) → Set
Map K V = ⟦ Mapₚ K ⟧ V

lookup : Map K V → K → Maybe V 
lookup (k→Bool , getter) k with k→Bool k in eq
... | false = nothing
... | true = just (getter (k , subst T (sym eq) tt))

insert : (K → K → Bool) → K → V → Map K V → Map K V
insert _≗_ k v (k→Bool , getter) = (λ k₁ → (k ≗ k₁) ∨ k→Bool k₁) , λ where
  (k , prf) → {!!}
