{-# OPTIONS --type-in-type #-}
module Poly.Types.List where

--------------------------------------------------------------------------------

open import Data.Fin using (Fin; suc; zero; toℕ)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_,_)
open import Poly
open import Poly.Monoidal
open import Poly.Types.Maybe
open import Poly.SetFunctor

--------------------------------------------------------------------------------

listₚ : Poly
listₚ .Base = ℕ
listₚ .Fiber n = Fin n

List : Set → Set
List = ⟦ listₚ ⟧

nil : ∀{A : Set} → List A
nil = zero , λ ()

cons : ∀{A : Set} → A → List A → List A
cons a (tag , args) = (suc tag) , λ where
  zero → a
  (suc x) → args x

maybeₚ⇒listₚ : maybeₚ ⇒ listₚ
maybeₚ⇒listₚ .map-base = toℕ
maybeₚ⇒listₚ .map-fiber zero ()
maybeₚ⇒listₚ .map-fiber (suc zero) x = x

maybe⇒List : ∀{A : Set} → Maybe A → List A
maybe⇒List maybe = maybeₚ⇒listₚ ⟨$⟩ maybe

maybe-listₚ : Poly
maybe-listₚ = listₚ ◁ maybeₚ

Maybe-List : Set → Set
Maybe-List = ⟦ maybe-listₚ ⟧

empty : Maybe-List ℕ
empty = (zero , λ ()) , λ ()

just-nil : Maybe-List ℕ
just-nil = (suc zero , λ _ → zero ) , λ ()

-- just-cons : {A : Set} → A → List A → Maybe-List A
-- just-cons n (tag , args) = (suc tag , λ x → {!!}) , λ where
--   (fst , snd) → args {!!}
