{-# OPTIONS --type-in-type #-}
module Poly where

--------------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Fin hiding (_+_)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_; Morphism; const; id)
open import Poly.SetFunctor
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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
-- where @p(1)@ denotes a @P .Base@ and @p[i]@ denotes the function @P .Fiber i@.
--
-- We prefer the following equivalent form, as it more closely matches
-- agda's sigma syntax, which will be used henceforth:
--
-- p x ≔ Σ[ i ∈ I ] x^aᵢ
--
-- I is thus @P .Base@ and @aᵢ@ is @P .Fiber i@.
record Poly : Set where
  constructor poly
  field
    Base : Set
    Fiber : Base → Set

open Poly public

--------------------------------------------------------------------------------

-- | Interpretation of a Poly as a functor @Set → Set@
⟦_⟧ : ∀ {a b} → Poly → (Set a → Set b)
⟦ P ⟧ X = Σ[ tag ∈ P .Base ] (P .Fiber tag → X)

mapₚ : ∀{P : Poly} → ∀{A B : Set} → (A → B) → ⟦ P ⟧ A → ⟦ P ⟧ B
mapₚ f (tag , args) = tag , λ x → f (args x)

--------------------------------------------------------------------------------
-- Examples

-- | Building a monomial.
--
-- m y ≡ y³ 
--
-- m y ≡ Σ[ i ∈ Fin 1 ] ((i → Set) → y)  
m : Poly
m .Base = Fin 1
m .Fiber = λ where
  zero → Fin 3

-- | Building a Polynomial.
--
-- data P x = Foo x x x | Bar x x | Baz x | Qux
-- 
-- P y ≡ y³ + y² + y + 1
-- 
-- P y ≡ Σ [ i ∈ Fin 4 ] y^aᵢ 
--   where
--     a : Fin 4 → Set
-- 
-- y^(aᵢ) ≡ a i → y
p : Poly
p .Base = Fin 4
p .Fiber  = λ where
  zero →  Fin 2
  (suc zero) → Fin 1
  (suc (suc zero)) →  Fin 1
  (suc (suc (suc zero))) → Fin 0

-- | P y ≡ Σ [ i ∈ Fin 4 ] y^aᵢ 
_ : ∀ {Y : Set} → (⟦ p ⟧ Y) ≡ (Σ[ i ∈ Fin 4 ] (p .Fiber i → Y))
_ = refl

-- | Adding coefficients to a polynomial.
--
-- data Q y = Foo y y y | Bar y y | Baz Bool y | Qux
-- 
-- Q y ≡ y³ + y² + (2 · y) + y⁰
-- 
-- Q y ≡ Σ[ i ∈ Fin 5 ] y^aᵢ
q : Poly
q .Base  = Fin 5
q .Fiber = λ where
  zero →  Fin 3
  (suc zero) → Fin 2
  (suc (suc zero)) → Fin 1
  (suc (suc (suc zero))) → Fin 1
  (suc (suc (suc (suc zero)))) → Fin 0

--------------------------------------------------------------------------------

-- | S × Yᵀ
monomial : Set → Set → Poly
(monomial S T) .Base = S
(monomial S T) .Fiber  = λ _ → T

-- | S × X⁰
constant : Set → Poly
constant S = monomial S ⊥

-- | The variable X.
--
-- ⟦ 𝕐 ⟧ = id
𝕐 : Poly
𝕐 = monomial ⊤ ⊤

open _≃_

⟦⟧-𝕐 : ⟦ 𝕐 ⟧ ≃ id
⟦⟧-𝕐 .to (_ , f) = f tt
⟦⟧-𝕐 .from x = tt , λ _ → x

-- | Power.
𝕐^_ : Set → Poly
𝕐^_ = monomial ⊤

⟦⟧-𝕐^ : ∀{ T : Set} → ⟦ 𝕐^ T ⟧ ≃ Morphism T
⟦⟧-𝕐^ .to (_ , f) = f
⟦⟧-𝕐^ .from = tt ,_

⟦⟧-constant : ∀{S : Set} → ⟦ constant S ⟧ ≃ const S
⟦⟧-constant .to (s , _) = s
⟦⟧-constant .from = _, λ()

_$'_ : ∀{A B : Set} → (A → B) → A → B
f $' x = f x

--------------------------------------------------------------------------------

-- | A map between two Polynomials
infixr 0 _⇒_
record _⇒_ (P Q : Poly) : Set where
  constructor poly-map
  field
    map-base : P .Base → Q .Base 
    map-fiber : (tag : P .Base ) → Q .Fiber (map-base tag) → P .Fiber tag

open _⇒_ public

-- | Transform a map between polynomials into a natural
-- | transformation (a polymorphic function).
_⟨$⟩_ : ∀{P Q : Poly} → P ⇒ Q → ⟦ P ⟧ ↝ ⟦ Q ⟧
p⇒q ⟨$⟩ (tag , args) = map-base p⇒q tag , λ qargs → args (map-fiber p⇒q tag qargs)

idₚ : ∀{P : Poly} → P ⇒ P
idₚ .map-base tag = tag
idₚ .map-fiber tag args = args

-- | higher order identity
inert : ∀{A B : Set} → ⟦ monomial ⊤ ⊤ ⟧ (A → B) → A → B
inert (tt , f) a = f tt a

infixr 4 _⨟ₚ_
_⨟ₚ_ : ∀{P Q R : Poly} → P ⇒ Q → Q ⇒ R → P ⇒ R
(p⇒q ⨟ₚ q⇒r) .map-base = q⇒r .map-base ∘ p⇒q .map-base
(p⇒q ⨟ₚ q⇒r) .map-fiber ptag rargs = p⇒q .map-fiber ptag (map-fiber q⇒r (map-base p⇒q ptag) rargs)

polymap : ∀{P Q : Poly} → ⟦ P ⟧ ↝ ⟦ Q ⟧ → P ⇒ Q
polymap f .map-base ptag = proj₁ (f (ptag , id))
polymap f .map-fiber ptag qargs = proj₂ (f (ptag , id)) qargs

⟦⟧-monomial : ∀{S T : Set} → ⟦ monomial S T ⟧ ≡ const S ×₁ Morphism T
⟦⟧-monomial = refl

