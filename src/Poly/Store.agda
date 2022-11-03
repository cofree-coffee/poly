{-# OPTIONS --type-in-type #-}
module Poly.Store where

--------------------------------------------------------------------------------

open import Data.List
open import Data.Nat hiding (_+_)
open import Data.Product 
open import Poly

--------------------------------------------------------------------------------

private variable
  A B C D S T I J O S₁ I₁ J₁ O₁ S₂ I₂ J₂ O₂ : Set
  P Q R : Poly

--------------------------------------------------------------------------------

-- | Σ[ s ∈ S ] x^a_s
store : Set → Poly
store S = monomial S S 

Store : Set → Set → Set
Store S =  ⟦ store S ⟧  

pos : Store S A → S
pos (here , view) = here

peek : S → Store S A → A
peek s (here , view) = view s

peeks : (S → S) → Store S A → A
peeks f (here , view) = view (f here)

seek : S → Store S A → Store S A
seek s (here , view) = (s , view)

seeks : (S → S) → Store S A → Store S A
seeks f (here , view) = (f here , view)

-- NOTE: I don't have a Functor definition handy.
experiment : ∀{F : Set → Set} → (∀{X Y : Set} → (X → Y) → F X → F Y) → (S → F S) → Store S A → F A
experiment map f st = map (λ s → peek s st) (f (pos st))
