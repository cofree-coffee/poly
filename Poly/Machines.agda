{-# OPTIONS --type-in-type #-}
module Poly.Machines where

--------------------------------------------------------------------------------

open import Data.Bool hiding (T)
open import Function
open import Data.Fin
open import Data.List
open import Data.Nat 
open import Data.Product 
import Data.String as String
open import Data.Unit
open import Data.Vec hiding (_++_)
open import Poly

--------------------------------------------------------------------------------

private variable
  A B C D S T I O : Set
  P Q R : Poly

--------------------------------------------------------------------------------

-- | S · xˢ → O · xᴵ
Moore : Set → Set → Set → Set
Moore S I O = monomial S S ⇒ monomial O I

-- | SI · xˢ → O · x¹
Mealy : Set → Set → Set → Set
Mealy S I O = monomial (S × I) S ⇒ monomial O (Fin 1)

-- | Evaluate one step of a Moore Machine with a given input @I@.
step : I → S → Moore S I O → (O × S)
step i s bot = bot .map-tag s , bot .map-args s i 

-- | Turn the crank on a Moore Machine with a list of inputs @I@.
process : S → List I → Moore S I O → List O × S
process s [] bot = [] , s
process s (i ∷ xs) bot =
  let (o , s') = step i s bot
      (os , s'') = process s' xs bot
  in o ∷ os , s''

--------------------------------------------------------------------------------
-- Examples

helloMoore : Moore String.String String.String String.String 
helloMoore .map-tag  = id
helloMoore .map-args  = λ _ name → "hello, " String.++ name

latch : Moore ℕ ℕ ℕ
map-tag latch = id
map-args latch = _⊔_

-- _ = {! step "David" "" helloMoore!}

-- _ = {! process 0 (1 ∷ 2 ∷ 2 ∷ 4 ∷ 3 ∷ 1 ∷ []) latch !}
