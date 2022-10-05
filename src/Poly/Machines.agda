{-# OPTIONS --type-in-type #-}
module Poly.Machines where

--------------------------------------------------------------------------------

open import Data.Bool hiding (T)
open import Function
open import Data.Fin
open import Data.List
open import Data.Nat 
open import Data.Product 
open import Data.String hiding (_++_)
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

mkMoore : (S → O) → (S → I → S) → Moore S I O
(mkMoore get put) .map-tag = get
(mkMoore get put) .map-args tag = put tag

-- | SI · xˢ → O · x¹
Mealy : Set → Set → Set → Set
Mealy S I O = monomial (S × I) S ⇒ monomial O ⊤

mkMealy : (S × I → (S × O)) → Mealy S I O
(mkMealy f) .map-tag  = proj₂ ∘ f
(mkMealy f) .map-args tag = λ _ → (proj₁ ∘ f) tag

-- | Evaluate one step of a Moore Machine with a given input @I@ and
-- | state @S@.
step-moore : I → S → Moore S I O → (O × S)
step-moore i s bot = bot .map-tag s , bot .map-args s i 

-- | Turn the crank on a Moore Machine with a list of inputs @I@.
process-moore : S → List I → Moore S I O → List O × S
process-moore s [] bot = [] , s
process-moore s (i ∷ xs) bot =
  let (o , s') = step-moore i s bot
      (os , s'') = process-moore s' xs bot
  in o ∷ os , s''

-- | Evaluate one step of a Mealy Machine with a given input @I@ and
-- | state @S@.
step-mealy : I → S → Mealy S I O → (O × S)
step-mealy i s bot = (bot .map-tag (s , i) , bot .map-args (s , i) tt)

-- | Turn the crank on a Mealy Machine with a list of inputs @I@.
process : S → List I → Mealy S I O → List O × S
process s [] bot = [] , s
process s (i ∷ xs) bot =
  let (o , s') = step-mealy i s bot
      (os , s'') = process s' xs bot
  in o ∷ os , s''

--------------------------------------------------------------------------------
-- Examples

helloMoore : Moore String String String 
helloMoore = mkMoore (λ name → "hello, " String.++ name) λ _ → id 

helloStep = step-moore "Brendan" "David" helloMoore
helloProcess = process-moore "foo" (("bar" ∷ "baz" ∷ "qux" ∷ [])) helloMoore

latch : Moore ℕ ℕ ℕ
map-tag latch = id
map-args latch = _⊔_

latchProcess = process-moore 0 (1 ∷ 2 ∷ 2 ∷ 4 ∷ 3 ∷ 1 ∷ []) latch 

delay : Moore S S S
delay = mkMoore id λ _ → id

delayStep = step-moore 1 0 delay
delayProcess = process-moore 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) delay

delay' : Mealy S S S
delay' = mkMealy id

--------------------------------------------------------------------------------
-- TODO: A Mealy Machine for converting binary numbers to their 2's complement.

data Bin : Set where
  ⟨⟩ : Bin
  _i : Bin → Bin
  _o : Bin → Bin

2s-complement : Mealy Bool Bool Bool
2s-complement = mkMealy λ where
  (false , false) → (false , false)
  (false , true) → (true , true)
  (true , input) → (true , not input)

example : List Bool
example = true ∷ false ∷ true ∷ false ∷ false ∷ []

exampleResult : List Bool
exampleResult = false ∷ true ∷ true ∷ false ∷ false ∷ []

