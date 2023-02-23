{-# OPTIONS --type-in-type #-}
module Poly.Types.Store where

--------------------------------------------------------------------------------

open import Data.Product using (_,_)
open import Poly

--------------------------------------------------------------------------------

-- | Σ[ s ∈ S ] x^a_s
store : Set → Poly
store S = monomial S S 

Store : Set → Set → Set
Store S =  ⟦ store S ⟧  

pos : ∀{S A : Set} → Store S A → S
pos (here , view) = here

peek : ∀{S A : Set} → S → Store S A → A
peek s (here , view) = view s

peeks : ∀{S A : Set} → (S → S) → Store S A → A
peeks f (here , view) = view (f here)

seek : ∀{S A : Set} → S → Store S A → Store S A
seek s (here , view) = (s , view)

seeks : ∀{S A : Set} → (S → S) → Store S A → Store S A
seeks f (here , view) = (f here , view)

-- NOTE: I don't have a Functor definition handy.
experiment : ∀{S A : Set} → ∀{F : Set → Set} → (∀{X Y : Set} → (X → Y) → F X → F Y) → (S → F S) → Store S A → F A
experiment map f st = map (λ s → peek s st) (f (pos st))
