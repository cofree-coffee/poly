{-# OPTIONS --type-in-type #-}
module Poly.Lens where

--------------------------------------------------------------------------------

open import Data.Bool using (Bool; true; false)
open import Data.Product 
open import Poly
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

--------------------------------------------------------------------------------

Lens : Set → Set → Set → Set → Set
Lens S T A B = monomial S T ⇒ monomial A B

view : ∀{S T A B : Set} → Lens S T A B → S → A
view lens s = lens .map-base s

over : ∀{S T A B : Set} → Lens S T A B → (A → B) → S → T 
over lens f s = lens .map-fiber s (f (lens .map-base s))

set : ∀{S T A B : Set} → Lens S T A B → B → S → T
set lens b s = lens .map-fiber s b

lens : ∀{S T A B : Set} → (S → A) → (S → B → T) → Lens S T A B
(lens get set) .map-base = get
(lens get set) .map-fiber = set

projₗ : ∀{A B : Set} → Lens (A × B) (A × B) A A
projₗ = lens proj₁ λ where
  (fst , snd) → λ a → (a , snd)

projᵣ : ∀{A B : Set} → Lens (A × B) (A × B) B B
projᵣ = lens proj₂ λ where
  (fst , snd) → λ b → (fst , b)

--------------------------------------------------------------------------------

example : Bool
example = view (projₗ ⨟ₚ projᵣ) ((true , false) , false)

example2 : ((Bool × Bool) × Bool)
example2 = set (projₗ ⨟ₚ projᵣ) true ((true , false) , false)


-- view l (set l v s)  ≡ v
get-set : ∀{A B : Set} → (v : A) → (s : (A × B)) → view projₗ (set projₗ v s) ≡ v
get-set v s = refl

-- set l (view l s) s  ≡ s
set-view : ∀{A B : Set} → (s : (A × B)) → (set projₗ (view projₗ s) s) ≡ s
set-view s = refl

-- set l v' (set l v s) ≡ set l v' s
set-set : ∀{A B : Set} → (v : A) → (v' : A) → (s : (A × B)) → (set projₗ v' (set projₗ v s)) ≡ set projₗ v' s
set-set v v' s = refl
