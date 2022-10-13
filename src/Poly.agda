{-# OPTIONS --type-in-type #-}
module Poly where

--------------------------------------------------------------------------------

open import Data.Fin hiding (_+_)
open import Data.Bool hiding (T; _∨_)
open import Data.Sum
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥)
open import Function
open import Data.Product 

open import Poly.SetFunctor

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

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
  P Q R Z : Poly

--------------------------------------------------------------------------------

-- | Interpretation of a Poly as a functor @Set → Set@
⟦_⟧ : ∀ {a b} → Poly → (Set a → Set b)
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
  (suc (suc (suc zero))) → ⊤

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
  (suc (suc (suc (suc zero)))) → ⊤

--------------------------------------------------------------------------------

-- | S × Xᵀ
monomial : Set → Set → Poly
(monomial S T) .Tag = S
(monomial S T) .Args  = λ _ → T

-- | S × X⁰
constant : Set → Poly
constant S = monomial S ⊥

-- | The variable X.
--
-- ⟦ 𝐗 ⟧ = id
𝐗 : Poly
𝐗 = monomial ⊤ ⊤

-- | Power.
𝐗^_ : Set → Poly
𝐗^_ = monomial ⊤

--------------------------------------------------------------------------------

-- | A map between two Polynomials
infixr 0 _⇒_
record _⇒_ (P Q : Poly) : Set where
  no-eta-equality
  constructor poly-map
  field
    map-tag : P .Tag → Q .Tag 
    map-args : (tag : P .Tag ) → Q .Args (map-tag tag) → P .Args tag

open _⇒_ public

-- | Transform a map between polynomials into a natural
-- | transformation (a polymorphic function).
_⟨$⟩_ : P ⇒ Q → ⟦ P ⟧ ↝ ⟦ Q ⟧
p⇒q ⟨$⟩ (tag , args) = map-tag p⇒q tag , λ qargs → args (map-args p⇒q tag qargs)

idₚ : P ⇒ P
idₚ .map-tag tag = tag
idₚ .map-args tag args = args

infixr 4 _⨟ₚ_
_⨟ₚ_ : P ⇒ Q → Q ⇒ R → P ⇒ R
(p⇒q ⨟ₚ q⇒r) .map-tag = q⇒r .map-tag ∘ p⇒q .map-tag
(p⇒q ⨟ₚ q⇒r) .map-args ptag rargs = p⇒q .map-args ptag (map-args q⇒r (map-tag p⇒q ptag) rargs)

polymap : ⟦ P ⟧ ↝ ⟦ Q ⟧ → P ⇒ Q
polymap f .map-tag ptag = proj₁ (f (ptag , id))
polymap f .map-args ptag qargs = proj₂ (f (ptag , id)) qargs

⟦⟧-monomial : ⟦ monomial S T ⟧ ≡ const S ×₁ Morphism T
⟦⟧-monomial = refl

open _≃_

⟦⟧-𝐗 : ⟦ 𝐗 ⟧ ≃ id
⟦⟧-𝐗 .to (_ , f) = f tt
⟦⟧-𝐗 .from x = tt , λ _ → x

⟦⟧-𝐗^ : ⟦ 𝐗^ T ⟧ ≃ Morphism T
⟦⟧-𝐗^ .to (_ , f) = f
⟦⟧-𝐗^ .from = tt ,_

⟦⟧-constant : ⟦ constant S ⟧ ≃ const S
⟦⟧-constant .to (s , _) = s
⟦⟧-constant .from = _, λ()
