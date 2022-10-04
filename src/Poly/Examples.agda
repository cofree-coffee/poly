{-# OPTIONS --type-in-type #-}
module Poly.Examples where

--------------------------------------------------------------------------------

open import Data.Bool hiding (T)
open import Function
open import Data.Fin
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
-- Maybe 

maybeₚ : Poly
Tag maybeₚ = Fin 2
Args maybeₚ zero = Fin 0
Args maybeₚ (suc x) = Fin 1

Maybe : Set → Set
Maybe = ⟦ maybeₚ ⟧

just : A → Maybe A
just a = (suc zero) , λ _ → a

nothing : Maybe A
nothing = zero , (λ ())

case-maybe : B → (A → B) → Maybe A → B
case-maybe cnothing cjust (zero , args) = cnothing
case-maybe cnothing cjust (suc tag , args) = cjust (args zero)

--------------------------------------------------------------------------------
-- List 

listₚ : Poly
listₚ .Tag  = ℕ
listₚ .Args n = Fin n

List : Set → Set
List = ⟦ listₚ ⟧

nil : List A
nil = zero , λ ()

cons : A → List A → List A
cons a (tag , args) = (suc tag) , λ where
  zero → a
  (suc x) → args x

maybe⇒Listₚ : maybeₚ ⇒ listₚ
maybe⇒Listₚ .map-tag = toℕ
maybe⇒Listₚ .map-args zero ()
maybe⇒Listₚ .map-args (suc zero) x = x

maybe⇒List : Maybe A → List A
maybe⇒List maybe = maybe⇒Listₚ ⟨$⟩ maybe

--------------------------------------------------------------------------------
-- Vector 

vector : ℕ → Poly
(vector n) .Tag  = Fin 1
(vector n) .Args  = λ _ → Fin n

Vector : ℕ → Set → Set
Vector n = ⟦ vector n ⟧

vnil : Vector 0 A
vnil = zero , λ ()

vcons : {n : ℕ} → A → Vector n A → Vector (suc n) A
vcons a (tag , args) = tag , λ where
  zero → a
  (suc x) → args x

vector⇒list : ∀ (n : ℕ) → Vector n A → List A
vector⇒list n (tag , args) = n , args

list⇒vector : List A → Σ[ n ∈ ℕ ] Vector n A
list⇒vector (tag , args) = tag , zero , args
