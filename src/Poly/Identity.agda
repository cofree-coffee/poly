{-# OPTIONS --type-in-type #-}
module Poly.Identity where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Fin
open import Data.Product 
open import Data.Unit
open import Poly
open import Poly.Monoidal

--------------------------------------------------------------------------------

private variable
  A B C D S T I O : Set
  P Q R : Poly

--------------------------------------------------------------------------------

identity : ⟦ 𝐗 ⟧ A → A 
identity (tt , f) = f tt

Identity : Set → Set
Identity = ⟦ 𝐗 ⟧

runIdentity : Identity A → A
runIdentity (tt , args) = args tt

id' : Identity A → Identity A
id' id = idₚ {P = 𝐗} ⟨$⟩ id

id : A → A
id x = proj₂ (id' (tt , λ _ → x)) tt
