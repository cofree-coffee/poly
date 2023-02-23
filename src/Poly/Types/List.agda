{-# OPTIONS --type-in-type #-}
module Poly.Types.List where

--------------------------------------------------------------------------------

open import Data.Fin using (Fin; suc; zero; toℕ)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_,_)
open import Poly
open import Poly.Types.Maybe
open import Poly.SetFunctor

--------------------------------------------------------------------------------

listₚ : Poly
listₚ .Tag = ℕ
listₚ .Args n = Fin n

List : Set → Set
List = ⟦ listₚ ⟧

nil : ∀{A : Set} → List A
nil = zero , λ ()

cons : ∀{A : Set} → A → List A → List A
cons a (tag , args) = (suc tag) , λ where
  zero → a
  (suc x) → args x

maybeₚ⇒listₚ : maybeₚ ⇒ listₚ
maybeₚ⇒listₚ .map-tag = toℕ
maybeₚ⇒listₚ .map-args zero ()
maybeₚ⇒listₚ .map-args (suc zero) x = x

maybe⇒List : ∀{A : Set} → Maybe A → List A
maybe⇒List maybe = maybeₚ⇒listₚ ⟨$⟩ maybe
