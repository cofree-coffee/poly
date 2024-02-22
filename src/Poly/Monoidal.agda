{-# OPTIONS --type-in-type #-}
-- | Monoidal Products and Co-Products on Poly
module Poly.Monoidal where

--------------------------------------------------------------------------------

open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; [_,_]; inj₁; inj₂)
open import Function using (_∘_; id)
open import Poly
open import Poly.SetFunctor

open _≃_

--------------------------------------------------------------------------------

-- | P + Q
-- The Categorical Co-Product of two Polyonomials
--
-- P + Q ≔ ∑[ j ∈ I ] x^aᵢ + ∑[ j ∈ J ] y^bⱼ
infixr 6 _+_
_+_ : Poly → Poly → Poly
(P + Q) .Base = P .Base ⊎ Q .Base
(P + Q) .Fiber (inj₁ x) = P .Fiber x
(P + Q) .Fiber (inj₂ y) = Q .Fiber y

_+⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P + R ⇒ Q + Z
(p⇒q +⇒ r⇒z) .map-base (inj₁ ptag) = inj₁ (map-base p⇒q ptag)
(p⇒q +⇒ r⇒z) .map-base (inj₂ rtag) = inj₂ (map-base r⇒z rtag)
(p⇒q +⇒ r⇒z) .map-fiber (inj₁ ptag) = map-fiber p⇒q ptag
(p⇒q +⇒ r⇒z) .map-fiber (inj₂ rtag) = map-fiber r⇒z rtag

mergeₚ : ∀{P : Poly} → P + P ⇒ P
mergeₚ .map-base (inj₁ ptag) = ptag
mergeₚ .map-base (inj₂ ptag) = ptag
mergeₚ .map-fiber (inj₁ ptag) pargs = pargs
mergeₚ .map-fiber (inj₂ ptag) pargs = pargs

-- | Co-Product Left Inclusion
leftₚ : ∀{P Q : Poly} → P ⇒ (P + Q) 
leftₚ .map-tag = inj₁
leftₚ .map-args tag = id

-- | Co-Product Right Inclusion
rightₚ : ∀{P Q : Poly} → Q ⇒ (P + Q)
rightₚ .map-tag = inj₂
rightₚ .map-args tag = id

-- | Co-Product eliminator
eitherₚ : ∀{P Q R : Poly} → P ⇒ R → Q ⇒ R → (P + Q) ⇒ R
eitherₚ p⇒r q⇒r .map-base (inj₁ ptag) = p⇒r .map-base ptag
eitherₚ p⇒r q⇒r .map-base (inj₂ qtag) = q⇒r .map-base qtag
eitherₚ p⇒r q⇒r .map-fiber (inj₁ tag) = p⇒r .map-fiber tag
eitherₚ p⇒r q⇒r .map-fiber (inj₂ tag) = q⇒r .map-fiber tag

Sum : (I : Set) → (I → Poly) → Poly
Sum I P .Base = ∃[ i ] P i .Base
Sum I P .Fiber (i , ptag) = P i .Fiber ptag

infix 2 Sum
syntax Sum I (λ i → P) = Σₚ[ i ∈ I ] P

⟦⟧-+ : ∀{P Q : Poly} → ⟦ P + Q ⟧ ≃ ⟦ P ⟧ +₁ ⟦ Q ⟧
⟦⟧-+ .to (inj₁ ptag , x) = inj₁ (ptag , x)
⟦⟧-+ .to (inj₂ qtag , y) = inj₂ (qtag , y)
⟦⟧-+ .from (inj₁ (ptag , x)) = inj₁ ptag , x
⟦⟧-+ .from (inj₂ (qtag , y)) = inj₂ qtag , y

⟦⟧-Sum : {I : Set} → {P : I → Poly} → ⟦ Σₚ[ i ∈ I ] (P i) ⟧ ≃ (Σ₁[ i ∈ I ] ⟦ P i ⟧)
⟦⟧-Sum .to ((i , ptag) , f) = i , ptag , f
⟦⟧-Sum .from (i , ptag , f) = (i , ptag) , f

--------------------------------------------------------------------------------

-- | P ◁ Q
-- Composition of Polyonomial Functors
--
-- ⟦ P ◁ Q ⟧ ≡ ⟦ P ⟧ ∘ ⟦ Q ⟧
-- Σ ? Π ?   ≡ Σ Π (Σ Π)
_◁_ : Poly → Poly → Poly
(P ◁ Q) .Base = Σ[ ptag ∈ P .Base ] (P .Fiber ptag → Q .Base) 
(P ◁ Q) .Fiber  (ptag , f) =  Σ[ pargs ∈ P .Fiber ptag ] Q .Fiber (f pargs)

⟦⟧-◁ : ∀{P Q : Poly} → ⟦ P ◁ Q ⟧ ≃ ⟦ P ⟧ ∘ ⟦ Q ⟧
⟦⟧-◁ .to ((ptag , qtag) , f) = ptag , λ pargs → qtag pargs , λ qargs → f (pargs , qargs)
⟦⟧-◁ .from (ptag , f) = (ptag , λ pargs → proj₁ (f pargs)) , λ{ (pargs , qargs) → proj₂ (f pargs) qargs }

id-◁-intro : (P : Poly) → P ⇒ 𝕐 ◁ P
id-◁-intro _ .map-base p = tt , λ _ → p
id-◁-intro _ .map-fiber p (_ , a) = a

◁-id-intro : (P : Poly) → P ⇒ P ◁ 𝕐
◁-id-intro _ .map-base p = p , (λ _ → tt)
◁-id-intro _ .map-fiber p (a , _) = a

◁-id-elim : (P : Poly) → P ◁ 𝕐 ⇒ P
◁-id-elim _ .map-base (p , _) = p
◁-id-elim _ .map-fiber (p , _) a = a , tt

id-◁-elim : (P : Poly) → 𝕐 ◁ P  ⇒ P
id-◁-elim _ .map-base (_ , p) = p tt
id-◁-elim _ .map-fiber (_ , p) a = tt , a

x² : {X : Set} → Poly
x² {X} = monomial (Fin 1) (X × X)

x²' : {X : Set} → Poly
Base x²' = Fin 1
Fiber (x²' {X}) = λ _ → X × X

_ : {X : Set} → x² {X = X} ≡ x²' {X = X}
_ = refl

x³ : {X : Set} → Poly
x³ {X} = monomial (Fin 1) (X × X × X)

x²◁x³ : {X : Set} → Poly
x²◁x³ {X} = x² {X} ◁ x³ {X}

x²◁x³' : {X : Set} → Poly
Base (x²◁x³' {X}) = Σ[ x²-base ∈ Fin 1 ] (X × X → Fin 1)
Fiber (x²◁x³' {X}) = λ where
  (x²-base , f) → Σ[ x²-fib ∈ X × X ] (X × X × X)

_ : {X : Set} → x²◁x³ {X} ≡ x²◁x³' {X}
_ = refl

--------------------------------------------------------------------------------

-- | P × Q
--
-- The Binary Categorical Product
--
-- Σ[ (i , j) ∈ P .Base × Q .Base ] x^(aᵢ + bⱼ)
infixr 7 _×ₚ_
_×ₚ_ : Poly → Poly → Poly
(P ×ₚ Q) .Base  =  P .Base × Q .Base
(P ×ₚ Q) .Fiber (ptag , qtag) = P .Fiber ptag ⊎ Q .Fiber qtag

-- | _×ₚ_ fst eliminator
fst-×ₚ : ∀{P Q : Poly} → (P ×ₚ Q) ⇒ P
fst-×ₚ .map-base (ptag , qtag) = ptag
fst-×ₚ .map-fiber (ptag , qtag) pargs = inj₁ pargs

-- | _×ₚ_ snd eliminator
snd-×ₚ : ∀{P Q : Poly} → (P ×ₚ Q) ⇒ Q
snd-×ₚ .map-base (ptag , qtag) = qtag
snd-×ₚ .map-fiber (ptag , qtag) qargs = inj₂ qargs

swap-×ₚ : ∀{P Q : Poly} → (P ×ₚ Q) ⇒ (Q ×ₚ P)
swap-×ₚ .map-base (ptag , qtag) = qtag , ptag
swap-×ₚ .map-fiber (ptag , qtag) (inj₁ qargs) = inj₂ qargs
swap-×ₚ .map-fiber (ptag , qtag) (inj₂ pargs) = inj₁ pargs

dupe-×ₚ : ∀{P : Poly} → P ⇒ P ×ₚ P
dupe-×ₚ .map-base ptag =  ptag , ptag
dupe-×ₚ .map-fiber ptag (inj₁ pargs) = pargs
dupe-×ₚ .map-fiber ptag (inj₂ pargs) = pargs

_&&&_ : ∀{P Q R : Poly} → R ⇒ P → R ⇒ Q → R ⇒ (P ×ₚ Q)
(f &&& g) .map-base rtag =  map-base f rtag , map-base g rtag
(f &&& g) .map-fiber rtag (inj₁ pargs) = map-fiber f rtag pargs
(f &&& g) .map-fiber rtag (inj₂ qargs) = map-fiber g rtag qargs

⟦⟧-×ₚ : ∀{P Q : Poly} → ⟦ P ×ₚ Q ⟧ ≃ ⟦ P ⟧ ×₁ ⟦ Q ⟧
⟦⟧-×ₚ .to ((ptag , qtag) , f) = (ptag , λ pargs → f (inj₁ pargs)) , (qtag , λ qargs → f (inj₂ qargs))
⟦⟧-×ₚ .from ((ptag , f) , (qtag , g)) = (ptag , qtag) , [ f , g ]

-- | p ×ₚ q can be recovered as Product Bool (if _ then q else p)
Product : (I : Set) → (I → Poly) → Poly
(Product I f) .Base = ∀ (i : I) → f i .Base
(Product I f) .Fiber tags = Σ[ i ∈ I ] (f i) .Fiber (tags i)

infix 2 Product
syntax Product I (λ i → P) = Πₚ[ i ∈ I ] P

⟦⟧-Product : {I : Set} {P : I → Poly} → ⟦ Πₚ[ i ∈ I ] P i ⟧ ≃ (Π₁[ i ∈ I ] ⟦ P i ⟧)
⟦⟧-Product .to (ptag , f) i = ptag i , λ pargs → f (i , pargs)
⟦⟧-Product .from f = proj₁ ∘ f , λ (i , pargs) → proj₂ (f i) pargs

--------------------------------------------------------------------------------

-- | P ⊗ Q
-- Also called the Parallel Product of two Polynomials
--
-- P ⊗ Q ≔ ∑[ i ∈ P .Base × Q .Base ] y^(aᵢ × bⱼ)
infixr 7 _⊗_
_⊗_ : Poly → Poly → Poly
(P ⊗ Q) .Base  = Base P × Base Q
(P ⊗ Q) .Fiber (ptag , qtag) = Fiber P ptag × Fiber Q qtag

swap-⊗ : ∀{P Q : Poly} → P ⊗ Q ⇒ Q ⊗ P
swap-⊗ .map-base (ptag , qtag) = qtag , ptag
swap-⊗ .map-fiber tag (qargs , pargs) = pargs , qargs

dupe-⊗ : ∀{P : Poly} → P ⇒ P ⊗ P
dupe-⊗ .map-base ptag =  ptag , ptag
dupe-⊗ .map-fiber ptag (f , g) = f

-- | The parallel product represents day convolution.
⟦⟧-⊗ : ∀{P Q : Poly} → ⟦ P ⊗ Q ⟧ ≃ day ⟦ P ⟧ ⟦ Q ⟧
⟦⟧-⊗ {P = P} {Q = Q} .to ((ptag , qtag) , f) = P .Fiber ptag , Q .Fiber qtag , (λ pargs qargs → f (pargs , qargs)) , (ptag , id) , (qtag , id)
⟦⟧-⊗ .from (B , C , f , (ptag , b) , (qtag , c)) = (ptag , qtag) , λ (pargs , qargs) → f (b pargs) (c qargs)

--------------------------------------------------------------------------------

-- | P Ⓥ Q
--
-- Σ[ (i , j) ∈ P .Base × Q . Base] x^(aᵢ Ⓥ bⱼ)
infixr 8 _Ⓥ_
_Ⓥ_ : Poly → Poly → Poly
(P Ⓥ Q) .Base = P .Base × Q .Base
(P Ⓥ Q) .Fiber = λ where
  (ptag , qtag) →  Fiber P ptag ⊎ (Fiber P ptag × Fiber Q qtag) ⊎ Fiber Q qtag

--------------------------------------------------------------------------------

-- | P ∨ Q
--
-- P ∨ Q ≔ P + (P ⊗ Q) + Q
infixr 5 _∨_
_∨_ :  Poly → Poly → Poly
P ∨ Q = P + (P ⊗ Q) + Q

-- | _∨_ This Inclusion
This : ∀{P Q : Poly} → P ⇒ (P ∨ Q)
This .map-base ptag = inj₁ ptag
This .map-fiber ptag = id

-- | _∨_ That Inclusion
That : ∀{P Q : Poly} → Q ⇒ (P ∨ Q)
That .map-base qtag = inj₂ (inj₂ qtag)
That .map-fiber qtag = id

-- | _∨_ These Inclusion
These : ∀{P Q : Poly} → (P ⊗ Q) ⇒ (P ∨ Q)
These .map-base tags = inj₂ (inj₁ tags)
These .map-fiber tags = id

-- | _∨_ Eliminator
theseₚ : ∀{P Q R : Poly} → P ⇒ R → Q ⇒ R → (P ⊗ Q) ⇒ R → (P ∨ Q) ⇒ R
(theseₚ p⇒r q⇒r pq⇒r) .map-base  (inj₁ ptag) = map-base p⇒r ptag
(theseₚ p⇒r q⇒r pq⇒r) .map-base (inj₂ (inj₁ tags)) = map-base pq⇒r tags
(theseₚ p⇒r q⇒r pq⇒r) .map-base (inj₂ (inj₂ qtag)) = map-base q⇒r qtag
(theseₚ p⇒r q⇒r pq⇒r) .map-fiber (inj₁ ptag) args = map-fiber p⇒r ptag args
(theseₚ p⇒r q⇒r pq⇒r) .map-fiber (inj₂ (inj₁ tags)) args = map-fiber pq⇒r tags args
(theseₚ p⇒r q⇒r pq⇒r) .map-fiber (inj₂ (inj₂ qtag)) args = map-fiber q⇒r qtag args
--theseₚ p⇒r q⇒r pq⇒r = {!!}

--------------------------------------------------------------------------------

-- | P ⊘ Q
--
-- P ⊘ Q ≔ P + (P ×ₚ Q) + Q
infixr 4 _⊘_
_⊘_ : Poly → Poly → Poly
P ⊘ Q = P + (P ×ₚ Q) + Q

--------------------------------------------------------------------------------

-- | P ⊛ Q
--
-- P ⊛ Q ≔  P + (P Ⓥ Q) + Q
infixr 4 _⊛_
_⊛_ : Poly → Poly → Poly
P ⊛ Q = P + (P Ⓥ Q) + Q

--------------------------------------------------------------------------------

_×ₚ⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P ×ₚ R ⇒ Q ×ₚ Z
(p⇒q ×ₚ⇒ r⇒z) .map-base (ptag , rtag) = (map-base p⇒q ptag) , (map-base r⇒z rtag)
(p⇒q ×ₚ⇒ r⇒z) .map-fiber (ptag , rtag) (inj₁ qargs) = inj₁ (map-fiber p⇒q ptag qargs)
(p⇒q ×ₚ⇒ r⇒z) .map-fiber (ptag , rtag) (inj₂ zargs) = inj₂ (map-fiber r⇒z rtag zargs)

-- | Parallel composition of systems, eg. the Parallel Product of
-- natural transformations between polynomials.
--
--      -------
-- >--A-|-[ ]-|-B-->
-- >--C-|-[ ]-|-D--> 
--      -------
--
-- (Syˢ ⇒ Byᴬ) ⊗⇒ (Tyᵗ ⇒ Dyᶜ) ≡ STyˢᵗ ⇒ BDyᵃᶜ
_⊗⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P ⊗ R ⇒ Q ⊗ Z
(p⇒q ⊗⇒ r⇒z) .map-base (ptag , rtag) = (map-base p⇒q ptag) , (map-base r⇒z rtag)
(p⇒q ⊗⇒ r⇒z) .map-fiber (ptag , rtag) (qargs , zargs) = (map-fiber p⇒q ptag qargs) , (map-fiber r⇒z rtag zargs)

_◁⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P ◁ R ⇒ Q ◁ Z
(p⇒q ◁⇒ r⇒z) .map-base (ptag , parg→rtag) = (map-base p⇒q ptag) , λ qargs → map-base r⇒z (parg→rtag (map-fiber p⇒q ptag qargs))
(p⇒q ◁⇒ r⇒z) .map-fiber (ptag , parg→rtag) (qargs , zargs) = map-fiber p⇒q ptag qargs , map-fiber r⇒z (parg→rtag (map-fiber p⇒q ptag qargs)) zargs

_Ⓥ⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P Ⓥ  R ⇒ Q Ⓥ Z
(p⇒q Ⓥ⇒ r⇒z) .map-base (ptag , rtag) = map-base p⇒q ptag , map-base r⇒z rtag
(p⇒q Ⓥ⇒ r⇒z) .map-fiber (ptag , rtag) (inj₁ qargs) = inj₁ (map-fiber p⇒q ptag qargs)
(p⇒q Ⓥ⇒ r⇒z) .map-fiber (ptag , rtag) (inj₂ (inj₁ (qargs , zargs))) = inj₂ (inj₁ ((map-fiber p⇒q ptag qargs) , (map-fiber r⇒z rtag zargs)))
(p⇒q Ⓥ⇒ r⇒z) .map-fiber (ptag , rtag) (inj₂ (inj₂ zargs)) = inj₂ (inj₂ (map-fiber r⇒z rtag zargs))

_∨⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P ∨ R ⇒ Q ∨ Z
(p⇒q ∨⇒ r⇒z) .map-base (inj₁ ptag) = inj₁ (map-base p⇒q ptag)
(p⇒q ∨⇒ r⇒z) .map-base (inj₂ (inj₁ (ptag , rtag))) = inj₂ (inj₁ ((map-base p⇒q ptag) , (map-base r⇒z rtag)))
(p⇒q ∨⇒ r⇒z) .map-base (inj₂ (inj₂ rtag)) = inj₂ (inj₂ (map-base r⇒z rtag))
(p⇒q ∨⇒ r⇒z) .map-fiber (inj₁ ptag) args = map-fiber p⇒q ptag args
(p⇒q ∨⇒ r⇒z) .map-fiber (inj₂ (inj₁ (ptag , rtag))) (qargs , zargs) = (map-fiber p⇒q ptag qargs) , map-fiber r⇒z rtag zargs
(p⇒q ∨⇒ r⇒z) .map-fiber (inj₂ (inj₂ rtag)) args = map-fiber r⇒z rtag args
