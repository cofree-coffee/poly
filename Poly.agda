{-# OPTIONS --type-in-type #-}
module Poly where

--------------------------------------------------------------------------------

open import Data.Bool hiding (T)
open import Function
open import Data.Fin
open import Data.Nat 
open import Data.Product 
open import Data.String
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

open Poly

private variable
  A B S T I O : Set
  P Q R : Poly

-- | Interpretation of a Poly as a Type
⟦_⟧ : Poly → Set → Set
⟦ P ⟧ X = Σ[ tag ∈ P .Tag ] (P .Args tag → X)

-- | All interpretations of Polys are Functors
pmap : (A → B) → ⟦ P ⟧ A → ⟦ P ⟧ B
pmap f (tag , args) = tag , λ x → f (args x)

maybeₚ : Poly
Tag maybeₚ = Fin 2
Args maybeₚ zero = Fin 0
Args maybeₚ (suc x) = Fin 1

Maybe : Set → Set
Maybe = ⟦ maybeₚ ⟧

just : A → Maybe A
just a = (suc zero) , λ _ → a

nothing : Maybe A
nothing = zero , (λ ())

case-maybe : B → (A → B) → Maybe A → B
case-maybe cnothing cjust (zero , args) = cnothing
case-maybe cnothing cjust (suc tag , args) = cjust (args zero)

listₚ : Poly
listₚ .Tag  = ℕ
listₚ .Args n = Fin n

List : Set → Set
List = ⟦ listₚ ⟧

nil : List A
nil = zero , λ ()

cons : A → List A → List A
cons a (tag , args) = (suc tag) , λ where
  zero → a
  (suc x) → args x

vector : ℕ → Poly
(vector n) .Tag  = Fin 1
(vector n) .Args  = λ _ → Fin n

Vector : ℕ → Set → Set
Vector n = ⟦ vector n ⟧

vnil : Vector 0 A
vnil = zero , λ ()

vcons : {n : ℕ} → A → Vector n A → Vector (suc n) A
vcons a (tag , args) = tag , λ where
  zero → a
  (suc x) → args x

vector⇒list : ∀ (n : ℕ) → Vector n A → List A
vector⇒list n (tag , args) = n , args

list⇒vector : List A → Σ[ n ∈ ℕ ] Vector n A
list⇒vector (tag , args) = tag , zero , args

--------------------------------------------------------------------------------

-- | S × Xᵀ
monomial : Set → Set → Poly
(monomial S T) .Tag = S
(monomial S T) .Args  = λ _ → T

_⊗_ : Poly → Poly → Poly
(P ⊗ Q) .Tag  = Tag P × Tag Q
(P ⊗ Q) .Args  (tagp , tagq) = Args P tagp × Args Q tagq

-- ⟦ P ◁ Q ⟧ ≡ ⟦ P ⟧ (⟦ Q ⟧ A)
-- Σ ? Π ?   ≡ Σ Π (Σ Π)
_◁_ : Poly → Poly → Poly
(P ◁ Q) .Tag = Σ[ ptag ∈ P .Tag ] (P .Args ptag → Q .Tag) 
(P ◁ Q) .Args  (ptag , f) =  Σ[ pargs ∈ P .Args ptag ] Q .Args (f pargs)

record _⇒_ (P Q : Poly) : Set where
  no-eta-equality
  constructor poly-map
  field
    map-tag : P .Tag → Q .Tag 
    map-args : (tag : P .Tag ) → Q .Args (map-tag tag) → P .Args tag

open _⇒_

-- | Transform a map between polynomials into a natural
-- | transformation (a polymorphic function).
_⟨$⟩_ : P ⇒ Q → ⟦ P ⟧ A → ⟦ Q ⟧ A
p⇒q ⟨$⟩ (tag , args) = map-tag p⇒q tag , λ qargs → args (map-args p⇒q tag qargs)

maybeToListₚ : maybeₚ ⇒ listₚ
maybeToListₚ .map-tag = toℕ
maybeToListₚ .map-args zero ()
maybeToListₚ .map-args (suc zero) x = x

maybeToList : Maybe A → List A
maybeToList maybe = maybeToListₚ ⟨$⟩ maybe

--------------------------------------------------------------------------------

-- | S · xˢ → O · xᴵ
moore : Set → Set → Set → Set
moore S I O = monomial S S ⇒ monomial O I

helloMoore : moore String String String 
helloMoore .map-tag  = id
helloMoore .map-args  = λ _ name → "hello, " ++ name

-- | SI · xˢ → O · x¹
mealy : Set → Set → Set → Set
mealy S I O = monomial (S × I) S ⇒ monomial O (Fin 1)

step : I → S → moore S I O → (O × S)
step i s bot = bot .map-tag s , bot .map-args s i 


