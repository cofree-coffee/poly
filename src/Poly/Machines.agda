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
Mealy S I O = monomial (S × I) S ⇒ monomial O ⊤

-- | Evaluate one step of a Moore Machine with a given input @I@.
step-moore : I → S → Moore S I O → (O × S)
step-moore i s bot = bot .map-tag s , bot .map-args s i 

-- | Turn the crank on a Moore Machine with a list of inputs @I@.
process-moore : S → List I → Moore S I O → List O × S
process-moore s [] bot = [] , s
process-moore s (i ∷ xs) bot =
  let (o , s') = step-moore i s bot
      (os , s'') = process-moore s' xs bot
  in o ∷ os , s''

-- | Evaluate one step of a Mealy Machine with a given input @I@.
step-mealy : I → S → Mealy S I O → (O × S)
step-mealy i s bot = (bot .map-tag (s , i) , bot .map-args (s , i) tt)

--------------------------------------------------------------------------------
-- Examples

helloMoore : Moore String.String String.String String.String 
helloMoore .map-tag  = id
helloMoore .map-args  = λ _ name → "hello, " String.++ name

helloStep =  step-moore "David" "" helloMoore
helloProcess = process-moore "" (("foo" ∷ "bar" ∷ "baz" ∷ [])) helloMoore

latch : Moore ℕ ℕ ℕ
map-tag latch = id
map-args latch = _⊔_

latchProcess = process-moore 0 (1 ∷ 2 ∷ 2 ∷ 4 ∷ 3 ∷ 1 ∷ []) latch 

delay : Moore S S S
delay .map-tag = id
delay .map-args tag = id

delayStep = step-moore 1 0 delay
delayProcess = process-moore 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) delay

delay' : Mealy S S S
delay' .map-tag (state , input) = state
delay' .map-args (state , input) x = input

-- .map-tag sets the output. map-args sets the new state
is-zero : Moore Bool ℕ Bool
is-zero .map-tag p = p
is-zero .map-args false x = {!!}
is-zero .map-args true x = {!!}
