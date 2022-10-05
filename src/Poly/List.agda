{-# OPTIONS --type-in-type #-}
module Poly.List where

--------------------------------------------------------------------------------

open import Data.Fin
open import Data.Nat 
open import Data.Product 
open import Poly
open import Poly.Maybe

--------------------------------------------------------------------------------

private variable
  A B C D S T I O : Set
  P Q R : Poly

--------------------------------------------------------------------------------

listₚ : Poly
listₚ .Tag  = ℕ
listₚ .Args n = Fin n

List : Set → Set
List = ⟦ listₚ ⟧

nil : List A
nil = zero , λ ()

cons : A → List A → List A
cons a (tag , args) = (suc tag) , λ where
  zero → a
  (suc x) → args x

maybe⇒Listₚ : maybeₚ ⇒ listₚ
maybe⇒Listₚ .map-tag = toℕ
maybe⇒Listₚ .map-args zero ()
maybe⇒Listₚ .map-args (suc zero) x = x

maybe⇒List : Maybe A → List A
maybe⇒List maybe = maybe⇒Listₚ ⟨$⟩ maybe
