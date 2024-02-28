module Poly.Machines.Pairing where

--------------------------------------------------------------------------------

open import Data.Unit
import Data.List
open import Data.Nat
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id; const)
open import Poly
open import Poly.Machines.Mealy
open import Poly.Machines.Moore
open import Poly.Monoidal
open import Poly.Monoidal.Coproduct
open import Poly.Monoidal.Tensor

--------------------------------------------------------------------------------

drop-⊤-fiber
  : ∀ {S A : Set}
  → monomial (S × A) (S × ⊤) ⇒ monomial (S × A) S
map-base drop-⊤-fiber = id
map-fiber drop-⊤-fiber _ s = s , tt

pair-machines
  : ∀ {S T A B : Set}
  → Moore S A B -- monomial S S ⇒ monomial B A
  → Mealy T B A -- monomial (T × B) T ⇒ monomial A ⊤
  → monomial S S ⊗ monomial T T ⇒ monomial B A ⊗ [ monomial B ⊤ , monomial A ⊤ ]
pair-machines {S} {T} {A} {B} moore mealy =
  moore ⊗⇒ ⊗-to-hom (compute-tensor ⨟ₚ drop-⊤-fiber ⨟ₚ mealy)

annihilate
  : ∀ {S T A B : Set}
  → Moore S A B
  → Mealy T B A
  → monomial S S ⊗ monomial T T ⇒ 𝕐
annihilate moore mealy = pair-machines moore mealy ⨟ₚ ⊗-second hom-to-𝕐 ⨟ₚ eval

trace-hom
  : ∀ { A B C : Set}
  → (A × B → C)
  → [ monomial A ⊤ , monomial B ⊤ ] ⇒ [ monomial A B , monomial C ⊤ ]
map-base (trace-hom f) Ay⇒By = record { map-base = λ a → f (a , (Ay⇒By .map-base a)) ; map-fiber = λ a _ → Ay⇒By .map-base a }
map-fiber (trace-hom _) Ay⇒By (a , tt) = a , tt

witness
  : ∀ {S T A B C : Set}
  → (B × A → C)
  → Moore S A B
  → Mealy T B A
  → monomial S S ⊗ monomial T T ⇒ monomial C ⊤
witness f moore mealy = pair-machines moore mealy ⨟ₚ ⊗-second (trace-hom f) ⨟ₚ eval

counter : Moore ℕ ⊤ ℕ -- monomial ℕ ℕ ⇒ monomial B ⊤
counter .map-base = id
counter .map-fiber n tt = ℕ.suc n

factorial : Mealy ℕ ℕ ⊤
map-base factorial (x , y) = tt
map-fiber factorial (x , y) tt = x * y

witnessed : ℕ y^ ℕ ⊗ ℕ y^ ℕ ⇒ (ℕ × ⊤) y^ ⊤
witnessed = witness id counter factorial

PairedMachine : Set → Set → Set → Set → Set
PairedMachine S T A B = monomial S S ⊗ monomial T T ⇒ monomial (B × A) ⊤

step-paired
  : ∀ { S T A B : Set}
  → (initialState : S × T)
  → PairedMachine S T A B
  → (S × T) × (B × A)
step-paired {S} {T} {A} {B} state machine =
  let
      observe : S × T → B × A
      observe = machine .map-base

      transition : (S × T) → ⊤ → S × T
      transition = machine .map-fiber
  in transition state tt , observe state

open Data.List
process-paired
  : ∀ { S T A B : Set}
  → ℕ
  → (S × T)
  → PairedMachine S T A B
  → List (S × T)
  → List (S × T)
process-paired zero _ _ acc = acc
process-paired (suc n) state machine acc =
  let
    (new-state , observation) = step-paired state machine
  in process-paired n new-state machine (new-state ∷ acc)

ex = process-paired 10 (1 , 1) witnessed []
