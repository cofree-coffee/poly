{-# OPTIONS --type-in-type #-}
module Poly.Machines where

--------------------------------------------------------------------------------

open import Data.Bool hiding (T)
open import Function
open import Data.Fin hiding (_+_)
open import Data.List
open import Data.Nat hiding (_+_)
open import Data.Product 
open import Data.String hiding (_++_)
open import Data.Sum
import Data.String as String
open import Data.Unit
open import Data.Vec hiding (_++_)
open import Poly
open import Poly.Monoidal
open import Poly.Profunctor

--------------------------------------------------------------------------------

private variable
  A B C D S T I J O S₁ I₁ J₁ O₁ S₂ I₂ J₂ O₂ : Set
  P Q R : Poly

--------------------------------------------------------------------------------

-- | Moore Machine:
--
-- S × I → S
-- S → O
--
-- S · xˢ → O · xᴵ
Moore : Set → Set → Set → Set
Moore S I O = monomial S S ⇒ monomial O I

mkMoore : (S → O) → (S → I → S) → Moore S I O
(mkMoore get put) .map-tag = get
(mkMoore get put) .map-args tag = put tag

disassemble-moore : Moore S I O → (S → O) × (S → I → S)
disassemble-moore bot = (λ s → bot .map-tag s) , λ s i → bot .map-args s i 

-- | evaluate one step of a moore machine with a given input @i@ and
-- | state @s@.
step-moore : I → S → Moore S I O → (O × S)
step-moore i s bot = bot .map-tag s , bot .map-args s i

-- | Turn the crank on a Moore Machine with a list of inputs @I@.
process-moore : S → List I → Moore S I O → List O × S
process-moore s [] bot = [] , s
process-moore s (i ∷ is) bot =
  let (o , s') = step-moore i s bot 
      (os , s'') = process-moore s' is bot
  in o ∷ os , s''

--------------------------------------------------------------------------------

-- | Mealy Machine:
-- 
-- S × I → S
-- S × I → O
--
-- | SI · xˢ → O · x¹
Mealy : Set → Set → Set → Set
Mealy S I O = monomial (S × I) S ⇒ monomial O ⊤

mkMealy : (S × I → (S × O)) → Mealy S I O
(mkMealy f) .map-tag  = proj₂ ∘ f
(mkMealy f) .map-args tag = λ _ → (proj₁ ∘ f) tag

-- | Evaluate one step of a Mealy Machine with a given input @I@ and
-- | state @S@.
step-mealy : I → S → Mealy S I O → (O × S)
step-mealy i s bot = bot .map-tag ( s , i) , bot .map-args (s , i) tt

-- | Turn the crank on a Mealy Machine with a list of inputs @I@.
process-mealy : S → List I → Mealy S I O → List O × S
process-mealy s [] bot = [] , s 
process-mealy s (i ∷ is) bot =
  let
    (o , s') = step-mealy i s bot
    (os , s'') = process-mealy s' is bot
  in  o ∷ os , s''

--------------------------------------------------------------------------------
-- Machine Composition

moore-+ : Moore S₁ I₁ O₁ → Moore S₂ I₂ O₂ → Moore (S₁ × S₂) (I₁ ⊎ I₂) (O₁ ⊎ O₂)
moore-+ m n .map-tag (s₁ , s₂) = inj₁ (map-tag m s₁) -- We must pick to project left or right arbitrarily
moore-+ m n .map-args (s₁ , s₂) (inj₁ i₁) = (map-args m s₁ i₁) , s₂
moore-+ m n .map-args (s₁ , s₂) (inj₂ i₂) = s₁ , map-args n s₂ i₂

moore-× : Moore S₁ I₁ O₁ → Moore S₂ I₂ O₂ → Moore (S₁ × S₂) (I₁ × I₂) (O₁ × O₂)
moore-× m n .map-tag (s₁ , s₂) =  m .map-tag s₁ , n .map-tag s₂
moore-× m n .map-args (s₁ , s₂) (i₁ , i₂) = (m .map-args s₁ i₁) , n .map-args s₂ i₂

mealy-+ : Mealy S₁ I₁ O₁ → Mealy S₂ I₂ O₂ → Mealy (S₁ × S₂) (I₁ ⊎ I₂) (O₁ ⊎ O₂)
mealy-+ m n .map-tag ((s₁ , s₂) , inj₁ i₁) = inj₁ (map-tag m (s₁ , i₁))
mealy-+ m n .map-tag ((s₁ , s₂) , inj₂ i₂) = inj₂ (map-tag n (s₂ , i₂))
mealy-+ m n .map-args ((s₁ , s₂) , inj₁ i₁) tt = (map-args m (s₁ , i₁) tt) , s₂ 
mealy-+ m n .map-args ((s₁ , s₂) , inj₂ i₂) tt = s₁ , (map-args n (s₂ , i₂) tt)

mealy-× : Mealy S₁ I₁ O₁ → Mealy S₂ I₂ O₂ → Mealy (S₁ × S₂) (I₁ × I₂) (O₁ × O₂)
mealy-× m n .map-tag ((s₁ , s₂) , i₁ , i₂) = (map-tag m (s₁ , i₁)) , (map-tag n (s₂ , i₂))
mealy-× m n .map-args ((s₁ , s₂) , i₁ , i₂) tt = (map-args m (s₁ , i₁) tt) , (map-args n (s₂ , i₂) tt)

--------------------------------------------------------------------------------
-- Examples

helloMoore : Moore String String String 
helloMoore = mkMoore (λ name → "hello, " String.++ name) λ _ → id 

goodbyeMoore : Moore String String String 
goodbyeMoore = mkMoore (λ name → "goodbye " String.++ name) λ _ → id 

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

2s-complement : Mealy Bool Bool Bool
2s-complement = mkMealy λ where
  (false , false) → (false , false)
  (false , true) → (true , true)
  (true , input) → (true , not input)

example : List Bool
example = true ∷ false ∷ true ∷ false ∷ false ∷ []

exampleResult : List Bool
exampleResult = false ∷ true ∷ true ∷ false ∷ false ∷ []
