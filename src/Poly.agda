{-# OPTIONS --type-in-type #-}
module Poly where

--------------------------------------------------------------------------------

open import Data.Fin hiding (_+_)
open import Data.Bool hiding (T; _∨_)
open import Data.Sum
open import Data.Unit as Unit
open import Function
open import Data.Product 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

--------------------------------------------------------------------------------


--------------------------------------------------------------------------------

-- A polynomial functor @p : Set → Set@ is any functor that is
-- isomorphic to a coproduct of representables, morphisms between them
-- is a natural transformation; the category is denoted @Poly@.
--
-- * A note on notation 
-- In David Spivak's work we typically see what the following
-- notation, which he calls Standard Form:
--
-- p ≔ Σ[ i ∈ p(1) ] y^p[i]
--
-- where @p(1)@ denotes a @P .Tag@ and @p[i]@ denotes the function @P .Args i@.
--
-- We prefer the following equivalent form, as it more closely matches
-- agda's sigma syntax, which will be used henceforth:
--
-- p x ≔ Σ[ i ∈ I ] x^aᵢ
--
-- I is thus @P .Tag@ and @aᵢ@ is @P .Args i@.
record Poly : Set where
  no-eta-equality
  constructor poly
  field
    Tag : Set
    Args : Tag → Set

open Poly public

private variable
  A B C D S T I O : Set
  P Q R : Poly

--------------------------------------------------------------------------------

-- | Interpretation of a Poly as a functor @Set → Set@
⟦_⟧ : Poly → (Set → Set)
⟦ P ⟧ X = Σ[ tag ∈ P .Tag ] (P .Args tag → X)

mapₚ : (A → B) → ⟦ P ⟧ A → ⟦ P ⟧ B
mapₚ f (tag , args) = tag , λ x → f (args x)

--------------------------------------------------------------------------------
-- Examples

-- | Building a monomial.
--
-- type MonomialExample = (i, (y₁, y₂, ..., yₐ))
-- 
-- MonomialExample ≡ i · yᵃ
--
-- m x ≡ x³ 
--
-- m x ≡ Σ[ i ∈ Fin 1 ] ((i → Set) → x)  
m : {X : Set} → Poly
(m {X}) .Tag = Fin 1
(m {X}) .Args = λ where
  zero → X × X × X

-- | Building a Polynomial.
--
-- data P x = Foo x x x | Bar x x | Baz x | Qux
-- 
-- P x ≡ x³ + x² + x + 0
-- 
-- P x ≡ Σ [ i ∈ Fin 4 ] x^aᵢ 
--   where
--     a : Fin 4 → Set
-- 
-- x^(aᵢ) ≡ a i → x
p : {X : Set} → Poly
(p {X}) .Tag = Fin 4
(p {X}) .Args  = λ where
  zero →  X × X × X
  (suc zero) →  X × X
  (suc (suc zero)) →  X
  (suc (suc (suc zero))) → Unit.⊤

-- | P x ≡ Σ [ i ∈ Fin 4 ] x^aᵢ 
_ : ∀ {X : Set} → (⟦ p {X = X} ⟧ X) ≡ (Σ[ i ∈ Fin 4 ] (p .Args i → X))
_ = refl

-- | Adding constants to a polynomial.
--
-- data Q x = Foo x x x | Bar x x | Baz Bool x | Qux
-- 
-- Q x ≡ x³ + x² + (2 · x) + x⁰
-- 
-- Q x ≡ Σ[ i ∈ Fin 5 ] x^aᵢ
q : {X : Set} → Poly
(q {X}) .Tag  = Fin 5
(q {X}) .Args = λ where
  zero →  X × X × X
  (suc zero) → X × X
  (suc (suc zero)) → X
  (suc (suc (suc zero))) → X
  (suc (suc (suc (suc zero)))) → Unit.⊤

--------------------------------------------------------------------------------

-- | S × Xᵀ
monomial : Set → Set → Poly
(monomial S T) .Tag = S
(monomial S T) .Args  = λ _ → T

--------------------------------------------------------------------------------

-- | A map between two Polynomials
record _⇒_ (P Q : Poly) : Set where
  no-eta-equality
  constructor poly-map
  field
    map-tag : P .Tag → Q .Tag 
    map-args : (tag : P .Tag ) → Q .Args (map-tag tag) → P .Args tag

open _⇒_ public

-- | Transform a map between polynomials into a natural
-- | transformation (a polymorphic function).
_⟨$⟩_ : P ⇒ Q → ⟦ P ⟧ A → ⟦ Q ⟧ A
p⇒q ⟨$⟩ (tag , args) = map-tag p⇒q tag , λ qargs → args (map-args p⇒q tag qargs)

_⨟_ : P ⇒ Q → Q ⇒ R → P ⇒ R
(p⇒q ⨟ q⇒r) .map-tag = q⇒r .map-tag ∘ p⇒q .map-tag
(p⇒q ⨟ q⇒r) .map-args ptag rargs = p⇒q .map-args ptag (map-args q⇒r (map-tag p⇒q ptag) rargs)

_∘ₚ_ : Q ⇒ R → P ⇒ Q → P ⇒ R
q⇒r ∘ₚ p⇒q = p⇒q ⨟ q⇒r

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
leftₚ .map-args tag =  id

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
-- Symmetric Monoidal Products on Poly

-- | P × Q
--
-- Σ[ (i , j) ∈ P .Tag × Q .Tag ] x^(aᵢ + bⱼ)
_×ₚ_ : Poly → Poly → Poly
(P ×ₚ Q) .Tag  =  P .Tag × Q .Tag
(P ×ₚ Q) .Args (ptag , qtag) = P .Args ptag ⊎ Q .Args qtag

fstₚ : (P ×ₚ Q) ⇒ P
fstₚ .map-tag (ptag , qtag) = ptag
fstₚ .map-args (ptag , qtag) pargs = inj₁ pargs

sndₚ : (P ×ₚ Q) ⇒ Q
sndₚ .map-tag (ptag , qtag) = qtag
sndₚ .map-args (ptag , qtag) qargs = inj₂ qargs

_&&&_ : R ⇒ P → R ⇒ Q → R ⇒ (P ×ₚ Q)
(f &&& g) .map-tag rtag =  map-tag f rtag , map-tag g rtag
(f &&& g) .map-args rtag (inj₁ pargs) = map-args f rtag pargs
(f &&& g) .map-args rtag (inj₂ qargs) = map-args g rtag qargs

-- | P ⊗ Q
-- Also called the Parallel Product of two Polynomials
--
-- P ⊗ Q ≔ ∑[ i ∈ P .Tag Q .Tag ] y^(aᵢ × bⱼ)
_⊗_ : Poly → Poly → Poly
(P ⊗ Q) .Tag  = Tag P × Tag Q
(P ⊗ Q) .Args  (ptag , qtag) = Args P ptag × Args Q qtag

-- | The Parallel Product of natural transformations between polynomials.
_***_ : ∀ {P Q R S} → P ⇒ R → Q ⇒ S → (P ⊗ Q) ⇒ (R ⊗ S)
(f *** g) .map-tag  (pt , qt) = map-tag f pt , map-tag g qt
(f *** g) .map-args (pt , qt) (rargs , sargs) = map-args f pt rargs , map-args g qt sargs

first : P ⇒ Q → (P ⊗ R) ⇒ (Q ⊗ R)
first p⇒q .map-tag (ptag , rtag) = map-tag p⇒q ptag , rtag
first p⇒q .map-args (ptag , rtag) (pargs , rargs) = map-args p⇒q ptag pargs , rargs

second : P ⇒ Q → (R ⊗ P) ⇒ (R ⊗ Q)
second p⇒q .map-tag (rtag , ptag) = rtag , map-tag p⇒q ptag
second p⇒q .map-args (rtag , ptag) (rargs , pargs) = rargs , map-args p⇒q ptag pargs

left : P ⇒ Q → (P + R) ⇒ (Q + R)
left p⇒q .map-tag (inj₁ ptag) = inj₁ (map-tag p⇒q ptag)
left p⇒q .map-tag (inj₂ rtag) = inj₂ rtag
left p⇒q .map-args (inj₁ ptag) args = map-args p⇒q ptag args
left p⇒q .map-args (inj₂ rtag) args = args

right : P ⇒ Q → (R + P) ⇒ (R + Q)
right p⇒q .map-tag (inj₁ rtag) = inj₁ rtag
right p⇒q .map-tag (inj₂ ptag) = inj₂ (map-tag p⇒q ptag)
right p⇒q .map-args (inj₁ rtag) args = args
right p⇒q .map-args (inj₂ ptag) args = map-args p⇒q ptag args

-- | P ∨ Q
--
-- NOTE: This is figure 7 from https://arxiv.org/pdf/2202.00534.pdf
-- and not figure 45.
--
-- Σ[ (i , j) ∈ P .Tag × Q . Tag] x^(aᵢ ∨ bⱼ)
_∨_ : Poly → Poly → Poly
(P ∨ Q) .Tag = P .Tag × Q .Tag
(P ∨ Q) .Args = λ where
  (ptag , qtag) →  Args P ptag ⊎ (Args P ptag × Args Q qtag) ⊎ Args Q qtag

--------------------------------------------------------------------------------

-- | Composition of Polyonomial Functors
-- ⟦ P ◁ Q ⟧ ≡ ⟦ P ⟧ (⟦ Q ⟧ A)
-- Σ ? Π ?   ≡ Σ Π (Σ Π)
_◁_ : Poly → Poly → Poly
(P ◁ Q) .Tag = Σ[ ptag ∈ P .Tag ] (P .Args ptag → Q .Tag) 
(P ◁ Q) .Args  (ptag , f) =  Σ[ pargs ∈ P .Args ptag ] Q .Args (f pargs)
