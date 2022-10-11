{-# OPTIONS --type-in-type #-}
-- | Monoidal Products and Co-Products on Poly
module Poly.Monoidal where

--------------------------------------------------------------------------------

open import Data.Product 
open import Data.Sum
open import Function
open import Poly

--------------------------------------------------------------------------------

private variable
  A B C D S T I O : Set
  P Q R Z : Poly

--------------------------------------------------------------------------------

-- | The Categorical Co-Product of two Polyonomials
--
-- P + Q ≔ ∑[ j ∈ I ] x^aᵢ + ∑[ j ∈ J ] y^bⱼ
_+_ : Poly → Poly → Poly
(P + Q) .Tag = P .Tag ⊎ Q .Tag
(P + Q) .Args (inj₁ x) = P .Args x
(P + Q) .Args (inj₂ y) = Q .Args y

-- | Co-Product Left Inclusion
leftₚ : P ⇒ (P + Q) 
leftₚ .map-tag = inj₁
leftₚ .map-args tag = id

-- | Co-Product Right Inclusion
rightₚ : Q ⇒ (P + Q)
rightₚ .map-tag = inj₂
rightₚ .map-args tag = id

-- | Co-Product eliminator
eitherₚ : P ⇒ R → Q ⇒ R → (P + Q) ⇒ R
eitherₚ f g .map-tag (inj₁ ptag) = f .map-tag ptag
eitherₚ f g .map-tag (inj₂ qtag) = g .map-tag qtag
eitherₚ f g .map-args (inj₁ tag) rargs = f .map-args tag rargs
eitherₚ f g .map-args (inj₂ tag) rargs = g .map-args tag rargs

--------------------------------------------------------------------------------

-- | P × Q
--
-- Σ[ (i , j) ∈ P .Tag × Q .Tag ] x^(aᵢ + bⱼ)
_×ₚ_ : Poly → Poly → Poly
(P ×ₚ Q) .Tag  =  P .Tag × Q .Tag
(P ×ₚ Q) .Args (ptag , qtag) = P .Args ptag ⊎ Q .Args qtag

fst-×ₚ : (P ×ₚ Q) ⇒ P
fst-×ₚ .map-tag (ptag , qtag) = ptag
fst-×ₚ .map-args (ptag , qtag) pargs = inj₁ pargs

snd-×ₚ : (P ×ₚ Q) ⇒ Q
snd-×ₚ .map-tag (ptag , qtag) = qtag
snd-×ₚ .map-args (ptag , qtag) qargs = inj₂ qargs

swap-×ₚ : (P ×ₚ Q) ⇒ (Q ×ₚ P)
swap-×ₚ .map-tag (ptag , qtag) = qtag , ptag
swap-×ₚ .map-args (ptag , qtag) (inj₁ qargs) = inj₂ qargs
swap-×ₚ .map-args (ptag , qtag) (inj₂ pargs) = inj₁ pargs

_&&&_ : R ⇒ P → R ⇒ Q → R ⇒ (P ×ₚ Q)
(f &&& g) .map-tag rtag =  map-tag f rtag , map-tag g rtag
(f &&& g) .map-args rtag (inj₁ pargs) = map-args f rtag pargs
(f &&& g) .map-args rtag (inj₂ qargs) = map-args g rtag qargs

--------------------------------------------------------------------------------

-- | P ⊗ Q
-- Also called the Parallel Product of two Polynomials
--
-- P ⊗ Q ≔ ∑[ i ∈ P .Tag Q .Tag ] y^(aᵢ × bⱼ)
_⊗_ : Poly → Poly → Poly
(P ⊗ Q) .Tag  = Tag P × Tag Q
(P ⊗ Q) .Args  (ptag , qtag) = Args P ptag × Args Q qtag

swap-⊗ : (P ⊗ Q) ⇒ (Q ⊗ P)
swap-⊗ .map-tag (ptag , qtag) = qtag , ptag
swap-⊗ .map-args tag (qargs , pargs) = pargs , qargs

-- | The Parallel Product of natural transformations between polynomials.
_***_ : ∀ {P Q R S} → P ⇒ R → Q ⇒ S → (P ⊗ Q) ⇒ (R ⊗ S)
(f *** g) .map-tag  (pt , qt) = map-tag f pt , map-tag g qt
(f *** g) .map-args (pt , qt) (rargs , sargs) = map-args f pt rargs , map-args g qt sargs

--------------------------------------------------------------------------------

-- | P ∨ₘ Q
--
-- NOTE: This is figure 7 from https://arxiv.org/pdf/2202.00534.pdf
-- and not figure 45.
--
-- Σ[ (i , j) ∈ P .Tag × Q . Tag] x^(aᵢ ∨ₘ bⱼ)
_∨ₘ_ : Poly → Poly → Poly
(P ∨ₘ Q) .Tag = P .Tag × Q .Tag
(P ∨ₘ Q) .Args = λ where
  (ptag , qtag) →  Args P ptag ⊎ (Args P ptag × Args Q qtag) ⊎ Args Q qtag
