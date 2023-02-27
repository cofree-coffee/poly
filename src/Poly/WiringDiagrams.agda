{-# OPTIONS --type-in-type #-}
module Poly.WiringDiagrams where

--------------------------------------------------------------------------------

open import Data.Bool.Base
open import Function using (_∘_; id)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base
open import Data.Fin using (Fin; suc; zero)
open import Data.List hiding (sum)
open import Data.Nat using (_⊔_; ℕ; zero)
import Data.Nat as ℕ
open import Poly
open import Poly.Lens
open import Poly.Machines
open import Poly.Monoidal
open import Poly.Profunctor
open import Poly.SetFunctor
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)

--------------------------------------------------------------------------------

-- | A wiring diagram is a poly map 'P ⇒ Q' where 'Q' is the outer
-- interface of the diagram and 'P' describes the interior mappings of
-- the diagram.
Diagram : Poly → Poly → Set
Diagram P Q = P ⇒ Q

--------------------------------------------------------------------------------

-- | Illustration available here:
-- https://www.youtube.com/live/kPfyHwibgzs?feature=share&t=1213
--
-- ACyᴬᴮ ⊗ Byᴬ ⇒ By¹
ACyᴬᴮ : ∀{A B C : Set} → Poly 
ACyᴬᴮ {A} {B} {C} = monomial (A × C) (A × B)

Byᴬ : ∀{A B : Set} → Poly
Byᴬ {A} {B} = monomial B A

By¹ : ∀{B : Set} → Poly
By¹ {B} = monomial B (Fin 1)

ACyᴬᴮ⊗Byᴬ⇒By¹ : ∀{A B C : Set} → Diagram (ACyᴬᴮ {A = A} {B = B} {C = C} ⊗ Byᴬ) By¹
ACyᴬᴮ⊗Byᴬ⇒By¹ .map-tag ((A , C) , B) = B
ACyᴬᴮ⊗Byᴬ⇒By¹ .map-args ((A , C) , B) zero = (A , B) , A


-- | ACByᴬᴮᴬ ⇒ By¹
ACByᴬᴮᴬ⇒By¹ : ∀{A B C : Set} → monomial (A × C × B) (A × B × A) ⇒ monomial B (Fin 1)
ACByᴬᴮᴬ⇒By¹ .map-tag (A , C , B) = B
ACByᴬᴮᴬ⇒By¹ .map-args (A , C , B) zero = A , (B , A)

-- ACyᴬᴮ⊗Byᴬ⇒By¹≡ACByᴬᴮᴬ⇒By¹ : ∀{A B C : Set} → ACyᴬᴮ⊗Byᴬ⇒By¹ ≡ ACByᴬᴮᴬ⇒By¹
-- ACyᴬᴮ⊗Byᴬ⇒By¹≡ACByᴬᴮᴬ⇒By¹ = refl


-- A²y ⊗ yᵃᵃ ⇒ y
--
-- ----         ----
-- |  |-A------A|  |
-- |  |-A------A|  |
-- ----         ----
--
A²y⊗yᵃᵃ⇒y : ∀{A : Set} → monomial (A × A) (Fin 1) ⇒ monomial (Fin 1) (Fin 1)
A²y⊗yᵃᵃ⇒y .map-tag (A₁ , A₂) = zero
A²y⊗yᵃᵃ⇒y .map-args (A₁ , A₂) zero = zero

-- | Receives a natural as input and outputs a natural.
-- 
-- ℕy^ℕ ⇒ ℕy^ℕ
--
-- monomial ℕ ℕ ⇒ monomial ℕ ℕ
delay : Moore ℕ ℕ ℕ 
delay = mds id

-- | Receive two ℕ as input and sum them as output.
--
-- ℕy^ℕ ⇒ ℕy^(ℕ × ℕ)
-- monomial ℕ ℕ ⇒ monomial ℕ (ℕ × ℕ)
sum : Moore ℕ (ℕ × ℕ) ℕ  
sum = mds λ (x , y) → x ℕ.+ y

-- | A wiring diagram describing the construction of a Fibbonaci sequence.
--
-- ℕy^(ℕ×ℕ) ⊗ ℕy^ℕ ⇒ ℕy¹
fib-wire : ∀{A : Set} → monomial A (A × A) ⊗ monomial A A ⇒ monomial A (Fin 1) 
fib-wire .map-tag (A , B) = B
fib-wire .map-args (A , B) zero = (A , B) , A

-- | The parallel composition of 'sum' and 'delay'
delay⊗⇒sum : monomial (ℕ × ℕ) (ℕ × ℕ) ⇒ monomial ℕ (ℕ × ℕ) ⊗ monomial ℕ ℕ
delay⊗⇒sum = sum ⊗⇒ delay

fib-machine : Moore (ℕ × ℕ) (Fin 1) ℕ
fib-machine = lmap-⇒ delay⊗⇒sum fib-wire

run-fib = process-moore' (1 , 1) (zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ []) fib-machine
