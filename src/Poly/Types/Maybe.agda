{-# OPTIONS --type-in-type #-}
module Poly.Types.Maybe where

--------------------------------------------------------------------------------

open import Data.Fin using (Fin; suc; zero)
open import Data.Product using (_,_)
open import Poly

--------------------------------------------------------------------------------

maybeₚ : Poly
Tag maybeₚ = Fin 2
Args maybeₚ zero = Fin 0
Args maybeₚ (suc x) = Fin 1

Maybe : Set → Set
Maybe = ⟦ maybeₚ ⟧

just : ∀{A : Set} → A → Maybe A
just a = (suc zero) , λ _ → a

nothing : ∀{A : Set} → Maybe A
nothing = zero , (λ ())

case-maybe : ∀{A B : Set} → B → (A → B) → Maybe A → B
case-maybe cnothing cjust (zero , args) = cnothing
case-maybe cnothing cjust (suc tag , args) = cjust (args zero)
