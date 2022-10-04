{-# OPTIONS --type-in-type #-}
module Poly where

--------------------------------------------------------------------------------

open import Data.Sum
open import Data.Bool hiding (T)
open import Function
open import Data.Fin hiding (_+_)
open import Data.Nat hiding (_+_)
open import Data.Product 
import Data.String as String
open import Data.Unit
open import Data.Vec hiding (_++_)

--------------------------------------------------------------------------------

{-

data P x = Foo x x x | Bar x x | Baz x | Qux

P x ≡ x³ + x² + x + 0

P x ≡ Σ [ i ∈ Fin 4 ] x^(a^i) 
  where
    a : Fin 4 → Set

x^(a^i) ≡ a i → x


data Q x = Foo x x x | Bar x x | Baz Bool x | Qux

Q x ≡ x³ + x² + (2 · x) + x⁰

Q x ≡ Σ[ i ∈ Fin 5 ] x^(a^i)

type MonomialExample = (i, (y₁, y₂, ..., yₐ))

MonomialExample ≡ i · yᵃ

-}

record Sigma (A : Set) (B : A → Set) : Set where
  constructor MkSigma
  field
    fst : A
    snd : B fst

sigmaExample : Sigma ℕ (Vec Bool)
Sigma.fst sigmaExample = 2
Sigma.snd sigmaExample = true ∷ false ∷ []

record Poly : Set where
  no-eta-equality
  constructor poly
  field
    Tag : Set        -- I aka Fin _
    Args : Tag → Set -- a

open Poly public

private variable
  A B C D S T I O : Set
  P Q R : Poly

-- | S × Xᵀ
monomial : Set → Set → Poly
(monomial S T) .Tag = S
(monomial S T) .Args  = λ _ → T

-- | Interpretation of a Poly as a Type
⟦_⟧ : Poly → Set → Set
⟦ P ⟧ X = Σ[ tag ∈ P .Tag ] (P .Args tag → X)

-- | All interpretations of Polys are Functors
pmap : (A → B) → ⟦ P ⟧ A → ⟦ P ⟧ B
pmap f (tag , args) = tag , λ x → f (args x)

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

--------------------------------------------------------------------------------

-- | Composition of Polyonomial Functors
-- ⟦ P ◁ Q ⟧ ≡ ⟦ P ⟧ (⟦ Q ⟧ A)
-- Σ ? Π ?   ≡ Σ Π (Σ Π)
_◁_ : Poly → Poly → Poly
(P ◁ Q) .Tag = Σ[ ptag ∈ P .Tag ] (P .Args ptag → Q .Tag) 
(P ◁ Q) .Args  (ptag , f) =  Σ[ pargs ∈ P .Args ptag ] Q .Args (f pargs)

--------------------------------------------------------------------------------
-- The Parallel Product of two Polynomials

_⊗_ : Poly → Poly → Poly
(P ⊗ Q) .Tag  = Tag P × Tag Q
(P ⊗ Q) .Args  (tagp , tagq) = Args P tagp × Args Q tagq

_⊗₁_ : ∀ {P Q R S} → P ⇒ R → Q ⇒ S → (P ⊗ Q) ⇒ (R ⊗ S)
(f ⊗₁ g) .map-tag  (pt , qt) = map-tag f pt , map-tag g qt
(f ⊗₁ g) .map-args (pt , qt) (rargs , sargs) = map-args f pt rargs , map-args g qt sargs

--------------------------------------------------------------------------------

-- | The Categorical Co-Product of two Polyonomials
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

eitherₚ : P ⇒ R → Q ⇒ R → (P + Q) ⇒ R
eitherₚ f g .map-tag (inj₁ ptag) = f .map-tag ptag
eitherₚ f g .map-tag (inj₂ qtag) = g .map-tag qtag
eitherₚ f g .map-args (inj₁ tag) rargs = f .map-args tag rargs
eitherₚ f g .map-args (inj₂ tag) rargs = g .map-args tag rargs

--------------------------------------------------------------------------------

-- | The Categorical Product of two Polynomials
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