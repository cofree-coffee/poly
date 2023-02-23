{-# OPTIONS --type-in-type #-}
module Poly.Types.Identity where

--------------------------------------------------------------------------------

open import Data.Product using (_,_; proj₂)
open import Data.Unit using (tt)
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
