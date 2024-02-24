{-# OPTIONS --type-in-type #-}
module Poly.Examples where

--------------------------------------------------------------------------------

open import Data.Fin hiding (_+_)
open import Data.Product using (Σ-syntax)
open import Poly
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- Examples

-- | Building a monomial.
--
-- m y ≡ y³ 
--
-- m y ≡ Σ[ i ∈ Fin 1 ] ((i → Set) → y)  
m : Poly
m .Base = Fin 1
m .Fiber = λ where
  zero → Fin 3

-- | Building a Polynomial.
--
-- data P x = Foo x x x | Bar x x | Baz x | Qux
-- 
-- P y ≡ y³ + y² + y + 1
-- 
-- P y ≡ Σ [ i ∈ Fin 4 ] y^aᵢ 
--   where
--     a : Fin 4 → Set
-- 
-- y^(aᵢ) ≡ a i → y
p : Poly
p .Base = Fin 4
p .Fiber  = λ where
  zero →  Fin 2
  (suc zero) → Fin 1
  (suc (suc zero)) →  Fin 1
  (suc (suc (suc zero))) → Fin 0

-- | P y ≡ Σ [ i ∈ Fin 4 ] y^aᵢ 
_ : ∀ {Y : Set} → (⟦ p ⟧ Y) ≡ (Σ[ i ∈ Fin 4 ] (p .Fiber i → Y))
_ = refl

-- | Adding coefficients to a polynomial.
--
-- data Q y = Foo y y y | Bar y y | Baz Bool y | Qux
-- 
-- Q y ≡ y³ + y² + (2 · y) + y⁰
-- 
-- Q y ≡ Σ[ i ∈ Fin 5 ] y^aᵢ
q : Poly
q .Base  = Fin 5
q .Fiber = λ where
  zero →  Fin 3
  (suc zero) → Fin 2
  (suc (suc zero)) → Fin 1
  (suc (suc (suc zero))) → Fin 1
  (suc (suc (suc (suc zero)))) → Fin 0
