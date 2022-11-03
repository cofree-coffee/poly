{-# OPTIONS --type-in-type #-}
module Poly.UI where

--------------------------------------------------------------------------------

open import Data.List
open import Data.Nat hiding (_+_)
open import Data.Product 
open import Poly
open import Poly.Store
open import Poly.Machines

--------------------------------------------------------------------------------

private variable
  A B C D S T I J O S₁ I₁ J₁ O₁ S₂ I₂ J₂ O₂ : Set
  P Q R : Poly

--------------------------------------------------------------------------------
-- Redux

mkReduxStore : (S → I → S) →  Moore S I S
(mkReduxStore reducer .map-tag) = proj₁
mkReduxStore reducer .map-args (state , tt) = reducer state

data Action : Set where
  Increment : Action
  Decrement : Action

reducer : ℕ → Action → ℕ
reducer n Increment = suc n
reducer zero Decrement = zero
reducer (suc n) Decrement = n

ReduxStore : Moore ℕ Action ℕ
ReduxStore = mkReduxStore reducer

reduxStep = process-moore 0 (Increment ∷ Increment ∷ Increment ∷ []) ReduxStore

--------------------------------------------------------------------------------
-- React

Component : Set → Set → Set
Component S A = monomial S S ⇒ monomial S A

renderₚ : S → Component S A → A
renderₚ s component = map-args {!!} s {!!}

render : Store S A → A
render component = peek (pos component) component

--------------------------------------------------------------------------------
-- Halogen (cofree)

--------------------------------------------------------------------------------
-- Sums 
