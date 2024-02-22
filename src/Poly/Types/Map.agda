{-# OPTIONS --type-in-type --allow-unsolved-metas #-}
module Poly.Types.Map where

--------------------------------------------------------------------------------

open import Data.Bool using (_∨_; Bool; true; false; T)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Unit using (tt)
open import Poly
open import Relation.Binary.PropositionalEquality using (subst; sym)

--------------------------------------------------------------------------------

Mapₚ : (K : Set) → Poly
(Mapₚ K) .Base = K → Bool
Mapₚ K .Fiber = λ k→bool →  Σ[ k ∈ K ] T (k→bool k)

Map : (K : Set) → (V : Set) → Set
Map K V = ⟦ Mapₚ K ⟧ V

lookup : ∀{K V : Set} → Map K V → K → Maybe V 
lookup (k→Bool , getter) k with k→Bool k in eq
... | false = nothing
... | true = just (getter (k , subst T (sym eq) tt))

insert : ∀{K V : Set} → (K → K → Bool) → K → V → Map K V → Map K V
insert _≗_ k v (k→Bool , getter) = (λ k₁ → (k ≗ k₁) ∨ k→Bool k₁) , λ where
  (k , prf) → {!!}
