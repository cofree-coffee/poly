{-# OPTIONS --type-in-type #-}
module Poly.Types.Vector where

--------------------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; Σ-syntax)
open import Poly
open import Poly.Types.List

--------------------------------------------------------------------------------

vector : ℕ → Poly
(vector n) .Tag  = Fin 1
(vector n) .Args  = λ _ → Fin n

Vector : ℕ → Set → Set
Vector n = ⟦ vector n ⟧

vnil : ∀{A : Set} → Vector 0 A
vnil = zero , λ ()

vcons : ∀{A : Set} → {n : ℕ} → A → Vector n A → Vector (suc n) A
vcons a (tag , args) = tag , λ where
  zero → a
  (suc x) → args x

vector⇒list : ∀{A : Set} → ∀ (n : ℕ) → Vector n A → List A
vector⇒list n (tag , args) = n , args

list⇒vector : ∀{A : Set} → List A → Σ[ n ∈ ℕ ] Vector n A
list⇒vector (tag , args) = tag , zero , args