module Poly.Machines.Examples where

--------------------------------------------------------------------------------

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; suc; zero)
open import Data.Integer using (ℤ)
import Data.Integer as ℤ
open import Data.Nat using (_⊔_; ℕ; zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; _∷_; [])
open import Function using (_∘_; id)
open import Poly
open import Poly.Machines.Mealy
open import Poly.Machines.Moore
open import Poly.Monoidal.Product
open import Poly.Monoidal.Tensor
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open import Relation.Nullary

--------------------------------------------------------------------------------

-- | A Mealy Machine for converting binary numbers to their 2's
-- | complement.
2s-complement : Mealy (Fin 2) Bool Bool
2s-complement .map-base (zero , i) = i
2s-complement .map-base (suc zero , false) = true
2s-complement .map-base (suc zero , true) = false
2s-complement .map-fiber (zero , false) tt = zero
2s-complement .map-fiber (zero , true) tt = suc zero
2s-complement .map-fiber (suc zero , i) tt = suc zero

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
map-base 3-state-dfsa = λ where
  zero → false
  (suc zero) → true
  (suc (suc zero)) → false
map-fiber 3-state-dfsa = λ where
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
mds f .map-base = id
mds f .map-fiber = λ _ a → f a

-- | An MDS given a partial function.
--
-- monomial (B ⊎ Fin 1) (B ⊎ Fin 1) ⇒ (monomial B A + monomial (Fin 1) (Fin 1))
mds-partial : ∀{A B : Set} → (A → B ⊎ Fin 1) → Moore (B ⊎ Fin 1) A (B ⊎ Fin 1)
mds-partial f .map-base = id
mds-partial f .map-fiber (inj₁ b) a = f a
mds-partial f .map-fiber (inj₂ zero) a = inj₂ zero

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

-- monomial S S ⇒ monomial (V ⊎ M) V 
Processor : Set → Set
Processor S = Moore S V (V ⊎ M) 

decide : ℤ → ℤ → (ℤ → V) → V → V
decide n c f v with n ℤ.≟ c
... | .true because ofʸ p = v
... | .false because ofⁿ ¬p = f n

-- | The Tape of a Turing machine has states (V^ℤ × ℤ), outputs V, and
-- inputs V x {L,R}, so as a Moore machine it is a lens:
-- 
--   (V^ℤ × ℤ)y^(V^ℤ × ℤ) ⇒ Vy^(V + {L,R})
--
--  monomial ((ℤ → V) × ℤ) ((ℤ → V) × ℤ) ⇒ monomial V (V ⊎ M)
tape : Moore ((ℤ → V) × ℤ) (V ⊎ M) V
tape .map-base (f , z) = f z
tape .map-fiber (f , c) (inj₂ Left) = f , (ℤ.pred c)
tape .map-fiber (f , c) (inj₂ Right) = f , (ℤ.suc c)
tape .map-fiber (f , c) (inj₁ in-v) = (λ n → decide n c f in-v) , c

-- monomial S S ⇒ monomial (V ⊎ M) V
processor
  : ∀ {S : Set}
  → (S → V ⊎ M)
  → (S → V → S)
  → Moore S V (V ⊎ M)
processor nextCommand updateState .map-base = nextCommand
processor nextCommand updateState .map-fiber = updateState

-- turing-wire : ∀{S : Set} → V y^ (V ⊎ M) ⊗ (V ⊎ M) y^ V ⇒ (Fin 1) y^ (Fin 1) 
turing-wire
  : ∀{S : Set}
  → V y^ (V ⊎ M) ⊗ (V ⊎ M) y^ V ⇒ (Fin 1) y^ (Fin 1) 
map-base turing-wire s = zero
map-fiber turing-wire (tape-output , inj₁ processor-output) zero = (inj₁ processor-output) , tape-output
map-fiber turing-wire (tape-output , inj₂ processr-output) zero = (inj₂ processr-output) , tape-output

tape⊗⇒processor
  : ∀ {S : Set}
  → (S → V ⊎ M)
  → (S → V → S)
  → ((ℤ → V) × ℤ) y^ ((ℤ → V) × ℤ) ⊗ S y^ S ⇒ V y^ (V ⊎ M) ⊗ (V ⊎ M) y^ V
tape⊗⇒processor nextCommand updateState =
  tape ⊗⇒ processor nextCommand updateState

turing-machine
  : ∀ {S : Set}
  → (S → V ⊎ M)
  → (S → V → S)
  → Moore ((((ℤ → V) × ℤ) × S)) (Fin 1) (Fin 1)
turing-machine {S} nextCommand updateState =
  uncompute-tensor ⨟ₚ tape⊗⇒processor nextCommand updateState ⨟ₚ turing-wire {S = S}

run-turing-machine : ∀{S : Set} → (S → V ⊎ M) → (S → V → S) → (s : S) → List (Fin 1) × ((((ℤ → V) × ℤ) × S))
run-turing-machine nextCommand updateState initialState =
  process-moore' (((λ _ → blank) , ℤ.+0) , initialState) (zero ∷ zero ∷ []) (turing-machine nextCommand updateState)

-- The 3-state busy beaver
data State : Set where
  a : State
  b : State
  c : State

-- nextCommand : State → V ⊎ M
-- nextCommand a = {!!}
-- nextCommand b = {!!}
-- nextCommand c = {!!}
-- nextCommand halt = {!!}
-- 
-- process : monomial State State ⇒ monomial (V ⊎ M) V
-- process = processor nextCommand {!!}

--------------------------------------------------------------------------------

-- | A Moore machine that sets its state to the max of the input ands
-- current state.
--
-- ℕy^ℕ ⇒ ℕy^ℕ
--
-- monomial ℕ ℕ ⇒ monomial ℕ ℕ
latch : Moore ℕ ℕ ℕ
map-base latch = id
map-fiber latch = _⊔_

run-latch = process-moore 0 (1 ∷ 2 ∷ 2 ∷ 4 ∷ 3 ∷ 1 ∷ []) latch 

-- | Counter takes unchanging input and produces as output the
-- sequence of natural numbers 0, 1, 2, 3, ... .
--
-- ℕy^ℕ ⇒ ℕy
--
-- monomial ℕ ℕ ⇒ monomial ℕ (Fin 1)
counter : Moore ℕ (Fin 1) ℕ
counter .map-base = id
counter .map-fiber n zero =  ℕ.suc n

run-counter = process-moore' 0 (zero ∷ zero ∷ zero ∷ zero ∷ []) counter

-- | A Moore machine that receives a constant input and outputs its
-- state.
--
-- >--1--[ ]--ℕ-->

-- ℕy^ℕ ⇒ ℕy
--
-- monomial ℕ ℕ ⇒ monomial ℕ (Fin 1)
repeater : Moore ℕ (Fin 1) ℕ
repeater .map-base n = n
repeater .map-fiber n zero = n

run-repeater = process-moore' 7 (zero ∷ zero ∷ zero ∷ []) repeater

-- | A Moore machine that receives a natural and outputs Fin 1.
--
-- >--ℕ--[ ]--1-->
--
-- ℕy^ℕ ⇒ y^ℕ
--
-- monomial ℕ ℕ ⇒ monomial (Fin 1) ℕ
const-1 : Moore ℕ ℕ (Fin 1) 
const-1 .map-base n = zero
const-1 .map-fiber n = id

run-const-one = process-moore' 1 (1 ∷ 2 ∷ 3 ∷ []) const-1

-- | The binary categorical product of 'const-1' and 'repeater'.
--
-- >--ℕ+1--[ ]--ℕ-->
--
-- ℕy^ℕ ⇒ ℕy^(ℕ + 1)
--
-- monomial ℕ ℕ ⇒ monomial ℕ (ℕ ⊎ Fin 1)
const-1+repeater' : Moore ℕ (ℕ ⊎ Fin 1) ℕ 
const-1+repeater' .map-base = id
const-1+repeater' .map-fiber n (inj₁ n') = n'
const-1+repeater' .map-fiber n (inj₂ zero) = n

-- | The binary categorical product implemented using more general
-- Poly combinators.
--
-- >--ℕ+1--[ ]--1×ℕ-->
--
-- ℕy^ℕ ⇒ y^ℕ × ℕy 
const-1+repeater : monomial ℕ ℕ ⇒ monomial (Fin 1) ℕ ×ₚ monomial ℕ (Fin 1) 
const-1+repeater = const-1 &&& repeater
-- const-1+repeater .map-base n = zero , n
-- const-1+repeater .map-fiber n (inj₁ n') = n'
-- const-1+repeater .map-fiber n (inj₂ zero) = n

run-const-1+repeater = process-moore' 0 (inj₁ 1 ∷ inj₂ zero ∷ inj₂ zero ∷ inj₁ 3 ∷ inj₂ zero ∷ []) const-1+repeater'

--------------------------------------------------------------------------------
-- Logic Gates

Gate : Set → Set → Set
Gate I O = Moore O I O

-- | NAND
--
-- +----------------+
-- | A | B | Output |
-- |-------+--------|
-- | 0 | 0 | 1      |
-- | 0 | 1 | 1      |
-- | 1 | 0 | 1      |
-- | 1 | 1 | 0      |
-- +----------------+
nandₚ : Gate (Fin 2 × Fin 2) (Fin 2)
nandₚ = mds λ where 
  (zero , zero) → suc zero
  (zero , suc zero) → suc zero
  (suc zero , zero) → suc zero
  (suc zero , suc zero) → zero

-- | NOT
--
-- +----------------+
-- | Input | Output |
-- |-------+--------|
-- | 1     | 0      |
-- | 0     | 1      |
-- +----------------+
not-wire : monomial (Fin 2) (Fin 2 × Fin 2) ⇒ monomial (Fin 2) (Fin 2)
not-wire .map-base s = s
not-wire .map-fiber s x = x , x

notₚ : Gate (Fin 2) (Fin 2)
notₚ = nandₚ ⨟ₚ not-wire

-- | AND
--
-- +----------------+
-- | A | B | Output |
-- |-------+--------|
-- | 0 | 0 | 0      |
-- | 0 | 1 | 0      |
-- | 1 | 0 | 0      |
-- | 1 | 1 | 1      |
-- +----------------+
and-wire : monomial (Fin 2) (Fin 2 × Fin 2) ⊗ monomial (Fin 2) (Fin 2 × Fin 2) ⇒ monomial (Fin 2) (Fin 2 × Fin 2)
and-wire .map-base (_ , snd) = snd
and-wire .map-fiber (fst , _) (in-fst , in-snd) = (in-fst , in-snd) , (fst , fst)

andₚ : Moore (Fin 2 × Fin 2) (Fin 2 × Fin 2) (Fin 2)
andₚ = uncompute-tensor ⨟ₚ nandₚ ⊗⇒ nandₚ ⨟ₚ and-wire

run = step-moore (suc zero , suc zero) ((zero , zero)) andₚ

-- | XOR
--
-- +----------------+
-- | A | B | Output |
-- |-------+--------|
-- | 0 | 0 | 0      |
-- | 0 | 1 | 1      |
-- | 1 | 0 | 1      |
-- | 1 | 1 | 0      |
-- +----------------+
xorₚ : Gate (Fin 2 × Fin 2) (Fin 2)
xorₚ = mds λ where
  (zero , zero) → zero
  (zero , suc zero) → suc zero
  (suc zero , zero) → suc zero
  (suc zero , suc zero) → zero

