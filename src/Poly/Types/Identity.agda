{-# OPTIONS --type-in-type #-}
module Poly.Types.Identity where

--------------------------------------------------------------------------------

open import Data.Product using (_,_; proj₂)
open import Data.Unit using (tt)
open import Poly
open import Poly.Monoidal

--------------------------------------------------------------------------------

identity : ∀{A : Set} → ⟦ 𝕐 ⟧ A → A 
identity (tt , f) = f tt

Identity : Set → Set
Identity = ⟦ 𝕐 ⟧

runIdentity : ∀{A : Set} → Identity A → A
runIdentity (tt , args) = args tt

id' : ∀{A : Set} → Identity A → Identity A
id' id = idₚ {P = 𝕐} ⟨$⟩ id

id : ∀{A : Set} → A → A
id x = proj₂ (id' (tt , λ _ → x)) tt
