{-# OPTIONS --type-in-type #-}
module Poly.Lens where

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
  A B C D S T I O : Set
  P Q R : Poly

--------------------------------------------------------------------------------

Lens : Set → Set → Set → Set → Set
Lens S T A B = monomial S T ⇒ monomial A B

view : Lens S T A B → S → A
view lens s = lens .map-tag s

over : Lens S T A B → (A → B) → S → T 
over lens f s = lens .map-args s (f (lens .map-tag s))

set : Lens S T A B → B → S → T
set lens b s = lens .map-args s b

lens : (S → A) → (S → B → T) → Lens S T A B
(lens get set) .map-tag = get
(lens get set) .map-args = set

projₗ : Lens (A × B) (A × B) A A
projₗ = lens proj₁ λ where
  (fst , snd) → λ a → (a , snd)

projᵣ : Lens (A × B) (A × B) B B
projᵣ = lens proj₂ λ where
  (fst , snd) → λ b → (fst , b)

--------------------------------------------------------------------------------

example : Bool
example = view (projₗ ∘ₚ projᵣ) ((true , false) , false)
