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
  A B C D S T I J O : Set
  P Q R : Poly

--------------------------------------------------------------------------------

Machine : Set → Set → Set → Set → Set
Machine S I J O = monomial (S × I) S ⇒ monomial O J

mkMachine : (S → I → O) → (S → I → J → S) → Machine S I J O
(mkMachine get put) .map-tag = uncurry get
(mkMachine get put) .map-args = λ{ (s , i) j → put s i j }

-- | Evaluate one step of a Machine with a given inputs @I@, @J@, and
-- | state @S@.
step : I → J → S → Machine S I J O → (O × S)
step i j s bot = bot .map-tag (s , i) , (bot .map-args (s , i)) j

-- | Turn the crank on a Machine with a list of inputs @I@ and @J@.
process : S → List (I × J) → Machine S I J O → List O × S
process s [] bot = [] , s
process s ( x ∷ xs) bot =
  let (i , j) = x
      (o , s') = step i j s bot
      (os , s'') = process s' xs bot
  in o ∷ os , s''

--------------------------------------------------------------------------------

-- | Moore Machine:
--
-- S × I → S
-- S → O
--
-- S · xˢ → O · xᴵ
Moore : Set → Set → Set → Set
Moore S I O = Machine S ⊤ I O

mkMoore : (S → O) → (S → I → S) → Moore S I O
(mkMoore get put) .map-tag = get ∘ proj₁
(mkMoore get put) .map-args tag = put (proj₁ tag)

-- | evaluate one step of a moore machine with a given input @i@ and
-- | state @s@.
step-moore : I → S → Moore S I O → (O × S)
step-moore i s = step tt i s 

-- | Turn the crank on a Moore Machine with a list of inputs @I@.
process-moore : S → List I → Moore S I O → List O × S
process-moore s xs = process s (Data.List.map (λ i → (tt , i)) xs)

--------------------------------------------------------------------------------

-- | Mealy Machine:
-- 
-- S × I → S
-- S × I → O
--
-- | SI · xˢ → O · x¹
Mealy : Set → Set → Set → Set
Mealy S I O = Machine S I ⊤ O

mkMealy : (S × I → (S × O)) → Mealy S I O
(mkMealy f) .map-tag  = proj₂ ∘ f
(mkMealy f) .map-args tag = λ _ → (proj₁ ∘ f) tag

-- | Evaluate one step of a Mealy Machine with a given input @I@ and
-- | state @S@.
step-mealy : I → S → Mealy S I O → (O × S)
step-mealy i s = step i tt s

-- | Turn the crank on a Mealy Machine with a list of inputs @I@.
process-mealy : S → List I → Mealy S I O → List O × S
process-mealy s xs = process s (Data.List.map (λ i → (i , tt)) xs)

--------------------------------------------------------------------------------
-- Examples

helloMoore : Moore String String String 
helloMoore = mkMoore (λ name → "hello, " String.++ name) λ _ → id 

helloStep = step-moore "Brendan" "David" helloMoore
helloProcess = process-moore "foo" (("bar" ∷ "baz" ∷ "qux" ∷ [])) helloMoore

latch : Moore ℕ ℕ ℕ
map-tag latch = id ∘ proj₁
map-args latch = _⊔_ ∘ proj₁

latchProcess = process-moore 0 (1 ∷ 2 ∷ 2 ∷ 4 ∷ 3 ∷ 1 ∷ []) latch 

delay : Moore S S S
delay = mkMoore id λ _ → id

delayStep = step-moore 1 0 delay
delayProcess = process-moore 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) delay

delay' : Mealy S S S
delay' = mkMealy id

--------------------------------------------------------------------------------
-- TODO: A Mealy Machine for converting binary numbers to their 2's complement.

2s-complement : Mealy Bool Bool Bool
2s-complement = mkMealy λ where
  (false , false) → (false , false)
  (false , true) → (true , true)
  (true , input) → (true , not input)

example : List Bool
example = true ∷ false ∷ true ∷ false ∷ false ∷ []

exampleResult : List Bool
exampleResult = false ∷ true ∷ true ∷ false ∷ false ∷ []

