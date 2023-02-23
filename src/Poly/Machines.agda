{-# OPTIONS --type-in-type #-}
module Poly.Machines where

--------------------------------------------------------------------------------

open import Data.Bool using (Bool; true; false)
open import Function using (_∘_; id)
open import Data.Fin using (Fin; suc; zero)
open import Data.Integer using (ℤ)
import Data.Integer as ℤ
open import Data.List
open import Data.Nat using (_⊔_; ℕ; zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Poly
open import Poly.Lens
open import Poly.Monoidal
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary

--------------------------------------------------------------------------------

-- | Moore Machine:
--
-- S × I → S
-- S → O
--
-- Sxˢ → Oxᴵ
Moore : Set → Set → Set → Set
Moore S I O = monomial S S ⇒ monomial O I

-- | We can build a 'Moore' from an output function and a transition
-- | function.
moore : ∀{S I O : Set} → (S → O) → (S → I → S) → Moore S I O
moore output transition .map-tag = output
moore output transition .map-args s = transition s

Moore≡Lens : ∀{S I O : Set} → Moore S I O ≡ Lens S S O I
Moore≡Lens = refl

-- | We can then recover the output and transition functions by
-- | eta-expanding around '.map-tag' and '.map-args'.
disassemble-moore : ∀{S I O : Set} → Moore S I O → (S → O) × (S → I → S)
disassemble-moore m = (λ s → m .map-tag s) , λ s i → m .map-args s i 

-- | Evaluate one step of a moore machine with a given input @i@ and
-- | state @s@.
step-moore : ∀{S I O : Set} → I → S → Moore S I O → (O × S)
step-moore i s bot = bot .map-tag s , bot .map-args s i

-- | Turn the crank on a Moore Machine with a list of inputs @I@.
process-moore' : ∀{S I O : Set} →  S → List I → Moore S I O → List O × S
process-moore' s [] bot = [] , s
process-moore' s (i ∷ is) bot =
  let (o , s') = step-moore i s bot 
      (os , s'') = process-moore' s' is bot
  in o ∷ os , s''

-- | Turn the crank on a Moore machine then emit the final state and
-- | the output associated with it.
process-moore : ∀{S I O : Set} →  S → List I → Moore S I O → O × S
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

mealy : ∀{S I O : Set} →  (S × I → (S × O)) → Mealy S I O
mealy f .map-tag  = proj₂ ∘ f
mealy f .map-args tag = λ _ → (proj₁ ∘ f) tag

-- | Evaluate one step of a Mealy Machine with a given input @I@ and
-- | state @S@.
step-mealy : ∀{S I O : Set} →  I → S → Mealy S I O → (O × S)
step-mealy i s bot = bot .map-tag ( s , i) , bot .map-args (s , i) tt

-- | Turn the crank on a Mealy Machine with a list of inputs @I@.
process-mealy : ∀{S I O : Set} →  S → List I → Mealy S I O → List O × S
process-mealy s [] bot = [] , s 
process-mealy s (i ∷ is) bot =
  let
    (o , s') = step-mealy i s bot
    (os , s'') = process-mealy s' is bot
  in  o ∷ os , s''

--------------------------------------------------------------------------------
-- Machine Composition

moore-+ : ∀{S₁ S₂ I₁ I₂ O₁ O₂ : Set} → Moore S₁ I₁ O₁ → Moore S₂ I₂ O₂ → Moore (S₁ × S₂) (I₁ ⊎ I₂) (O₁ ⊎ O₂)
moore-+ m n .map-tag (s₁ , s₂) = inj₁ (map-tag m s₁) -- We must pick to project left or right arbitrarily
moore-+ m n .map-args (s₁ , s₂) (inj₁ i₁) = (map-args m s₁ i₁) , s₂
moore-+ m n .map-args (s₁ , s₂) (inj₂ i₂) = s₁ , map-args n s₂ i₂

moore-× : ∀{S₁ S₂ I₁ I₂ O₁ O₂ : Set} → Moore S₁ I₁ O₁ → Moore S₂ I₂ O₂ → Moore (S₁ × S₂) (I₁ × I₂) (O₁ × O₂)
moore-× m n .map-tag (s₁ , s₂) =  m .map-tag s₁ , n .map-tag s₂
moore-× m n .map-args (s₁ , s₂) (i₁ , i₂) = (m .map-args s₁ i₁) , n .map-args s₂ i₂

mealy-+ : ∀{S₁ S₂ I₁ I₂ O₁ O₂ : Set} → Mealy S₁ I₁ O₁ → Mealy S₂ I₂ O₂ → Mealy (S₁ × S₂) (I₁ ⊎ I₂) (O₁ ⊎ O₂)
mealy-+ m n .map-tag ((s₁ , s₂) , inj₁ i₁) = inj₁ (map-tag m (s₁ , i₁))
mealy-+ m n .map-tag ((s₁ , s₂) , inj₂ i₂) = inj₂ (map-tag n (s₂ , i₂))
mealy-+ m n .map-args ((s₁ , s₂) , inj₁ i₁) tt = (map-args m (s₁ , i₁) tt) , s₂ 
mealy-+ m n .map-args ((s₁ , s₂) , inj₂ i₂) tt = s₁ , (map-args n (s₂ , i₂) tt)

mealy-× : ∀{S₁ S₂ I₁ I₂ O₁ O₂ : Set} → Mealy S₁ I₁ O₁ → Mealy S₂ I₂ O₂ → Mealy (S₁ × S₂) (I₁ × I₂) (O₁ × O₂)
mealy-× m n .map-tag ((s₁ , s₂) , i₁ , i₂) = (map-tag m (s₁ , i₁)) , (map-tag n (s₂ , i₂))
mealy-× m n .map-args ((s₁ , s₂) , i₁ , i₂) tt = (map-args m (s₁ , i₁) tt) , (map-args n (s₂ , i₂) tt)

--------------------------------------------------------------------------------

-- | A Mealy Machine for converting binary numbers to their 2's
-- | complement.
2s-complement : Mealy (Fin 2) Bool Bool
2s-complement .map-tag (zero , i) = i
2s-complement .map-tag (suc zero , false) = true
2s-complement .map-tag (suc zero , true) = false
2s-complement .map-args (zero , false) tt = zero
2s-complement .map-args (zero , true) tt = suc zero
2s-complement .map-args (suc zero , i) tt = suc zero

-- | The 2s complement of 001 is 111.
--
-- Note we have to reverse our list because we should be running the
-- algorithm from right to left.
run-2s-complement = process-mealy zero (true ∷ false ∷ false ∷ []) 2s-complement

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
mds : ∀{A B : Set} → (A → B) → Moore B A B
mds f .map-tag = id
mds f .map-args = λ _ a → f a

-- | An MDS given a partial function.
--
-- monomial (B ⊎ Fin 1) (B ⊎ Fin 1) ⇒ (monomial B A + monomial (Fin 1) (Fin 1))
mds-partial : ∀{A B : Set} → (A → B ⊎ Fin 1) → Moore (B ⊎ Fin 1) A (B ⊎ Fin 1)
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

decide : ℤ → ℤ → (ℤ → V) → V → V
decide n c f v with n ℤ.≟ c
... | .true because ofʸ p = v
... | .false because ofⁿ ¬p = f n

-- | The Tape of a Turing machine has states (V^ℤ × ℤ), outputs V, and
-- inputs V x {L,R}, so as a Moore machine it is a lens:
-- 
--   (V^ℤ × ℤ)y^(V^ℤ × ℤ) ⇒ Vy^(V × {L,R})
tape : monomial ((ℤ → V) × ℤ) ((ℤ → V) × ℤ) ⇒ monomial V (V × M)
tape .map-tag (f , c) = f c
tape .map-args (f , c) (v , Left) =  (λ n → decide n c f v) , ℤ.suc c
tape .map-args (f , c) (v , Right) =  (λ n → decide n c f v) , ℤ.pred c

processor : ∀{S : Set} → (S → V ⊎ M) → (S → V → S) → monomial S S ⇒ monomial (V ⊎ M) V 
processor nextCommand updateState .map-tag = nextCommand
processor nextCommand updateState .map-args = updateState

step-tape : V × M → ((ℤ → V) × ℤ) → monomial ((ℤ → V) × ℤ) ((ℤ → V) × ℤ) ⇒ monomial V (V × M) → V × ((ℤ → V) × ℤ)
step-tape v×m s tape =  tape .map-tag s , tape .map-args s v×m

-- The 3-state busy beaver
data State : Set where
  a : State
  b : State
  c : State
  halt : State

-- nextCommand : State → V ⊎ M
-- nextCommand a = {!!}
-- nextCommand b = {!!}
-- nextCommand c = {!!}
-- nextCommand halt = {!!}
-- 
-- process : monomial State State ⇒ monomial (V ⊎ M) V
-- process = processor nextCommand {!!}

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
