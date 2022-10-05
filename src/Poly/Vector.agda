{-# OPTIONS --type-in-type #-}
module Poly.Vector where

--------------------------------------------------------------------------------

open import Data.Fin
open import Data.Nat 
open import Data.Product 
open import Poly
open import Poly.List

--------------------------------------------------------------------------------

private variable
  A B C D S T I O : Set
  P Q R : Poly
  
--------------------------------------------------------------------------------

vector : ℕ → Poly
(vector n) .Tag  = Fin 1
(vector n) .Args  = λ _ → Fin n

Vector : ℕ → Set → Set
Vector n = ⟦ vector n ⟧

vnil : Vector 0 A
vnil = zero , λ ()

vcons : {n : ℕ} → A → Vector n A → Vector (suc n) A
vcons a (tag , args) = tag , λ where
  zero → a
  (suc x) → args x

vector⇒list : ∀ (n : ℕ) → Vector n A → List A
vector⇒list n (tag , args) = n , args

list⇒vector : List A → Σ[ n ∈ ℕ ] Vector n A
list⇒vector (tag , args) = tag , zero , args
