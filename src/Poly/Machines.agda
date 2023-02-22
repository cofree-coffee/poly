{-# OPTIONS --type-in-type #-}
module Poly.Machines where

--------------------------------------------------------------------------------

open import Agda.Builtin.Int
open import Data.Bool hiding (T)
open import Data.Maybe
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

-- | We can build a 'Moore' from an output function and a transition
-- | function.
moore : (S → O) → (S → I → S) → Moore S I O
moore output transition .map-tag = output
moore output transition .map-args s = transition s

-- | We can then recover the output and transition functions by
-- | eta-expanding around '.map-tag' and '.map-args'.
disassemble-moore : Moore S I O → (S → O) × (S → I → S)
disassemble-moore m = (λ s → m .map-tag s) , λ s i → m .map-args s i 

-- | Evaluate one step of a moore machine with a given input @i@ and
-- | state @s@.
step-moore : I → S → Moore S I O → (O × S)
step-moore i s bot = bot .map-tag s , bot .map-args s i

-- | Turn the crank on a Moore Machine with a list of inputs @I@.
process-moore' : S → List I → Moore S I O → List O × S
process-moore' s [] bot = [] , s
process-moore' s (i ∷ is) bot =
  let (o , s') = step-moore i s bot 
      (os , s'') = process-moore' s' is bot
  in o ∷ os , s''

-- | Turn the crank on a Moore machine then emit the final state and
-- | the output associated with it.
process-moore : S → List I → Moore S I O → O × S
process-moore s i bot =
  let (_ , s') = process-moore' s i bot
  in (bot .map-tag s') , s'

--------------------------------------------------------------------------------

-- | Mealy Machine:
-- 
-- S × I → S
-- S × I → O
--
-- | SI · xˢ → O · x¹
Mealy : Set → Set → Set → Set
Mealy S I O = monomial (S × I) S ⇒ monomial O ⊤

mealy : (S × I → (S × O)) → Mealy S I O
(mealy f) .map-tag  = proj₂ ∘ f
(mealy f) .map-args tag = λ _ → (proj₁ ∘ f) tag

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
-- TODO: A Mealy Machine for converting binary numbers to their 2's complement.

2s-complement : Mealy Bool Bool Bool
2s-complement = mealy λ where
  (false , false) → (false , false)
  (false , true) → (true , true)
  (true , input) → (true , not input)

example : List Bool
example = true ∷ false ∷ true ∷ false ∷ false ∷ []

exampleResult : List Bool
exampleResult = false ∷ true ∷ true ∷ false ∷ false ∷ []

--------------------------------------------------------------------------------

-- | Determinisitic Finite State Automata. The output 'Bool'
-- determines the accept states.
--
-- Syˢ ⇒ 2yᵃ
--
--  monomial fin fin ⇒ monomial Bool A
DFSA : Set → Set → Set
DFSA S A = Moore S A Bool

data Alphabet : Set where
  a₀ : Alphabet
  a₁ : Alphabet

-- | A 'DFSA' with 3 states.
--
-- 3y³ ⇒ 2yᵃ
--
-- monomial (Fin 3) (Fin 3) ⇒ monomial Bool Alphabet
3-state-dfsa : DFSA (Fin 3) Alphabet 
map-tag 3-state-dfsa = λ where
  zero → false
  (suc zero) → true
  (suc (suc zero)) → false
map-args 3-state-dfsa = λ where
  zero a₀ → suc zero
  zero a₁ → suc (suc zero)
  (suc zero) a₀ → suc (suc zero)
  (suc zero) a₁ → suc zero
  (suc (suc zero)) a₀ → zero
  (suc (suc zero)) a₁ → zero

run-3-state-dfsa = process-moore zero (a₀ ∷ a₁ ∷ a₀ ∷ a₁ ∷ a₀ ∷ []) 3-state-dfsa

--------------------------------------------------------------------------------

-- | A "memoryless dynamical system"
--
-- Byᴬ ⇒ Byᴬ
--
-- monomial B B ⇒ monomial B A
mds : (A → B) → Moore B A B
mds f .map-tag = id
mds f .map-args = λ _ a → f a

-- | An MDS given a partial function.
--
-- monomial (B ⊎ Fin 1) (B ⊎ Fin 1) ⇒ (monomial B A + monomial (Fin 1) (Fin 1))
mds-partial : (A → B ⊎ Fin 1) → Moore (B ⊎ Fin 1) A (B ⊎ Fin 1)
mds-partial f .map-tag = id
mds-partial f .map-args (inj₁ b) a = f a
mds-partial f .map-args (inj₂ zero) a = inj₂ zero

--------------------------------------------------------------------------------
-- Turing Machines

data V : Set where
  zero : V
  one : V
  blank : V

data M : Set where
  Left : M
  Right : M

Tape : Set → Set
Tape S = monomial S S ⇒ monomial V (V × M) 

Processor : Set → Set
Processor S = monomial S S ⇒ monomial (V ⊎ M) V 

inc : Int → Int
inc (pos n) = pos (suc n)
inc (negsuc zero) = pos (suc zero)
inc (negsuc (suc n)) = negsuc n

dec : Int → Int
dec (pos zero) = negsuc (suc zero)
dec (pos (suc n)) = pos n
dec (negsuc zero) = negsuc (suc zero)
dec (negsuc n) = negsuc (suc n)

bool : A → A → Bool → A
bool fls tru false = fls
bool fls tru true = tru

int-eq : Int → Int → Bool
int-eq (pos zero) (pos zero) = true
int-eq (pos zero) (pos (suc m)) = false
int-eq (pos (suc n)) (pos zero) = false
int-eq (pos (suc n)) (pos (suc m)) = int-eq (pos n) (pos m)
int-eq (pos n) (negsuc m) = false
int-eq (negsuc n) (pos m) = false
int-eq (negsuc zero) (negsuc zero) = true
int-eq (negsuc zero) (negsuc (suc m)) = false
int-eq (negsuc (suc n)) (negsuc zero) = false
int-eq (negsuc (suc n)) (negsuc (suc m)) = int-eq (negsuc n) (negsuc m)

-- | The Tape of a Turing machine has states (V^ℤ × ℤ), outputs V, and
-- inputs V x {L,R}, so as a Moore machine it is a lens:
-- 
--   (V^ℤ × ℤ)y^(V^ℤ × ℤ) ⇒ Vy^(V × {L,R})
tape : monomial ((Int → V) × Int) ((Int → V) × Int) ⇒ monomial V (V × M)
tape .map-tag (f , c) = f c
tape .map-args (f , c) (v , Left) =  (λ n → bool (f n) v (int-eq n c)) , dec c
tape .map-args (f , c) (v , Right) =  (λ n → bool (f n) v (int-eq n c)) , inc c

processor : (S → V ⊎ M) → (S → V → S) → monomial S S ⇒ monomial (V ⊎ M) V 
processor nextCommand updateState .map-tag = nextCommand
processor nextCommand updateState .map-args = updateState

step-tape : V × M → ((Int → V) × Int) → monomial ((Int → V) × Int) ((Int → V) × Int) ⇒ monomial V (V × M) → V × ((Int → V) × Int)
step-tape v×m s tape =  tape .map-tag s , tape .map-args s v×m

-- The 3-state busy beaver
data State : Set where
  a : State
  b : State
  c : State
  halt : State

nextCommand : State → V ⊎ M
nextCommand a = {!!}
nextCommand b = {!!}
nextCommand c = {!!}
nextCommand halt = {!!}

process : monomial State State ⇒ monomial (V ⊎ M) V
process = processor nextCommand {!!}

--------------------------------------------------------------------------------

-- | A Moore machine that recieves a natural as input and outputs a natural.
-- 
-- ℕy^ℕ ⇒ ℕy^ℕ
--
-- monomial ℕ ℕ ⇒ monomial ℕ ℕ
delay : Moore ℕ ℕ ℕ 
delay = mds id

run-delay = process-moore 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) delay

-- | A Moore machine that sets its state to the max of the input ands
-- current state.
--
-- ℕy^ℕ ⇒ ℕy^ℕ
--
-- monomial ℕ ℕ ⇒ monomial ℕ ℕ
latch : Moore ℕ ℕ ℕ
map-tag latch = id
map-args latch = _⊔_

run-latch = process-moore 0 (1 ∷ 2 ∷ 2 ∷ 4 ∷ 3 ∷ 1 ∷ []) latch 

-- | A Moore machine that receives a constant input and outputs its
-- state.
--
-- ℕy^ℕ ⇒ ℕy
--
-- monomial ℕ ℕ ⇒ monomial ℕ (Fin 1)
repeater : Moore ℕ (Fin 1) ℕ
repeater .map-tag n = n
repeater .map-args n zero = n

run-repeater = process-moore 7 (zero ∷ zero ∷ zero ∷ []) repeater

-- | A Moore machine that receives a natural and outputs Fin 1.
--
-- ℕy^ℕ ⇒ y^ℕ
--
-- monomial ℕ ℕ ⇒ monomial (Fin 1) ℕ
const-1 : Moore ℕ ℕ (Fin 1) 
const-1 .map-tag n = zero
const-1 .map-args n = id

run-const-one = process-moore zero (1 ∷ 2 ∷ 3 ∷ []) const-1

-- | ℕy^ℕ ⇒ ℕy^(ℕ + 1)
--
-- monomial ℕ ℕ ⇒ monomial ℕ (ℕ ⊎ Fin 1)
const-1+repeater' : Moore ℕ (ℕ ⊎ Fin 1) ℕ 
const-1+repeater' .map-tag = id
const-1+repeater' .map-args n (inj₁ n') = n'
const-1+repeater' .map-args n (inj₂ zero) = n

-- | ℕy^ℕ ⇒ y^ℕ × ℕy 
const-1+repeater : monomial ℕ ℕ ⇒ monomial (Fin 1) ℕ ×ₚ monomial ℕ (Fin 1) 
const-1+repeater = const-1 &&& repeater
-- const-1+repeater .map-tag n = zero , n
-- const-1+repeater .map-args n (inj₁ n') = n'
-- const-1+repeater .map-args n (inj₂ zero) = n
