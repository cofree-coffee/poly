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
(P + Q) .Tag = P .Tag ⊎ Q .Tag
(P + Q) .Args (inj₁ x) = P .Args x
(P + Q) .Args (inj₂ y) = Q .Args y

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
eitherₚ f g .map-tag (inj₁ ptag) = f .map-tag ptag
eitherₚ f g .map-tag (inj₂ qtag) = g .map-tag qtag
eitherₚ f g .map-args (inj₁ tag) rargs = f .map-args tag rargs
eitherₚ f g .map-args (inj₂ tag) rargs = g .map-args tag rargs

mergeₚ : ∀{P : Poly} → P + P ⇒ P
mergeₚ .map-tag (inj₁ ptag) = ptag
mergeₚ .map-tag (inj₂ ptag) = ptag
mergeₚ .map-args (inj₁ ptag) pargs = pargs
mergeₚ .map-args (inj₂ ptag) pargs = pargs

Sum : (I : Set) → (I → Poly) → Poly
Sum I P .Tag = ∃[ i ] P i .Tag
Sum I P .Args (i , ptag) = P i .Args ptag

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
(P ◁ Q) .Tag = Σ[ ptag ∈ P .Tag ] (P .Args ptag → Q .Tag) 
(P ◁ Q) .Args  (ptag , f) =  Σ[ pargs ∈ P .Args ptag ] Q .Args (f pargs)

⟦⟧-◁ : ∀{P Q : Poly} → ⟦ P ◁ Q ⟧ ≃ ⟦ P ⟧ ∘ ⟦ Q ⟧
⟦⟧-◁ .to ((ptag , qtag) , f) = ptag , λ pargs → qtag pargs , λ qargs → f (pargs , qargs)
⟦⟧-◁ .from (ptag , f) = (ptag , λ pargs → proj₁ (f pargs)) , λ{ (pargs , qargs) → proj₂ (f pargs) qargs }

--------------------------------------------------------------------------------

-- | P × Q
--
-- The Binary Categorical Product
--
-- Σ[ (i , j) ∈ P .Tag × Q .Tag ] x^(aᵢ + bⱼ)
infixr 7 _×ₚ_
_×ₚ_ : Poly → Poly → Poly
(P ×ₚ Q) .Tag  =  P .Tag × Q .Tag
(P ×ₚ Q) .Args (ptag , qtag) = P .Args ptag ⊎ Q .Args qtag

-- | _×ₚ_ fst eliminator
fst-×ₚ : ∀{P Q : Poly} → (P ×ₚ Q) ⇒ P
fst-×ₚ .map-tag (ptag , qtag) = ptag
fst-×ₚ .map-args (ptag , qtag) pargs = inj₁ pargs

-- | _×ₚ_ snd eliminator
snd-×ₚ : ∀{P Q : Poly} → (P ×ₚ Q) ⇒ Q
snd-×ₚ .map-tag (ptag , qtag) = qtag
snd-×ₚ .map-args (ptag , qtag) qargs = inj₂ qargs

swap-×ₚ : ∀{P Q : Poly} → (P ×ₚ Q) ⇒ (Q ×ₚ P)
swap-×ₚ .map-tag (ptag , qtag) = qtag , ptag
swap-×ₚ .map-args (ptag , qtag) (inj₁ qargs) = inj₂ qargs
swap-×ₚ .map-args (ptag , qtag) (inj₂ pargs) = inj₁ pargs

dupe-×ₚ : ∀{P : Poly} → P ⇒ P ×ₚ P
dupe-×ₚ .map-tag ptag =  ptag , ptag
dupe-×ₚ .map-args ptag (inj₁ pargs) = pargs
dupe-×ₚ .map-args ptag (inj₂ pargs) = pargs

_&&&_ : ∀{P Q R : Poly} → R ⇒ P → R ⇒ Q → R ⇒ (P ×ₚ Q)
(f &&& g) .map-tag rtag =  map-tag f rtag , map-tag g rtag
(f &&& g) .map-args rtag (inj₁ pargs) = map-args f rtag pargs
(f &&& g) .map-args rtag (inj₂ qargs) = map-args g rtag qargs

⟦⟧-×ₚ : ∀{P Q : Poly} → ⟦ P ×ₚ Q ⟧ ≃ ⟦ P ⟧ ×₁ ⟦ Q ⟧
⟦⟧-×ₚ .to ((ptag , qtag) , f) = (ptag , λ pargs → f (inj₁ pargs)) , (qtag , λ qargs → f (inj₂ qargs))
⟦⟧-×ₚ .from ((ptag , f) , (qtag , g)) = (ptag , qtag) , [ f , g ]

-- | p ×ₚ q can be recovered as Product Bool (if _ then q else p)
Product : (I : Set) → (I → Poly) → Poly
(Product I f) .Tag = ∀ (i : I) → f i .Tag
(Product I f) .Args tags = Σ[ i ∈ I ] (f i) .Args (tags i)

infix 2 Product
syntax Product I (λ i → P) = Πₚ[ i ∈ I ] P

⟦⟧-Product : {I : Set} {P : I → Poly} → ⟦ Πₚ[ i ∈ I ] P i ⟧ ≃ (Π₁[ i ∈ I ] ⟦ P i ⟧)
⟦⟧-Product .to (ptag , f) i = ptag i , λ pargs → f (i , pargs)
⟦⟧-Product .from f = proj₁ ∘ f , λ (i , pargs) → proj₂ (f i) pargs

--------------------------------------------------------------------------------

-- | P ⊗ Q
-- Also called the Parallel Product of two Polynomials
--
-- P ⊗ Q ≔ ∑[ i ∈ P .Tag × Q .Tag ] y^(aᵢ × bⱼ)
infixr 7 _⊗_
_⊗_ : Poly → Poly → Poly
(P ⊗ Q) .Tag  = Tag P × Tag Q
(P ⊗ Q) .Args (ptag , qtag) = Args P ptag × Args Q qtag

swap-⊗ : ∀{P Q : Poly} → P ⊗ Q ⇒ Q ⊗ P
swap-⊗ .map-tag (ptag , qtag) = qtag , ptag
swap-⊗ .map-args tag (qargs , pargs) = pargs , qargs

dupe-⊗ : ∀{P : Poly} → P ⇒ P ⊗ P
dupe-⊗ .map-tag ptag =  ptag , ptag
dupe-⊗ .map-args ptag (f , g) = f

-- | The Parallel Product of natural transformations between polynomials.
_***_ : ∀ {P Q R S : Poly} → P ⇒ R → Q ⇒ S → P ⊗ Q ⇒ R ⊗ S
(f *** g) .map-tag  (pt , qt) = map-tag f pt , map-tag g qt
(f *** g) .map-args (pt , qt) (rargs , sargs) = map-args f pt rargs , map-args g qt sargs

-- | The parallel product represents day convolution.
⟦⟧-⊗ : ∀{P Q : Poly} → ⟦ P ⊗ Q ⟧ ≃ day ⟦ P ⟧ ⟦ Q ⟧
⟦⟧-⊗ {P = P} {Q = Q} .to ((ptag , qtag) , f) = P .Args ptag , Q .Args qtag , (λ pargs qargs → f (pargs , qargs)) , (ptag , id) , (qtag , id)
⟦⟧-⊗ .from (B , C , f , (ptag , b) , (qtag , c)) = (ptag , qtag) , λ (pargs , qargs) → f (b pargs) (c qargs)

--------------------------------------------------------------------------------

-- | P Ⓥ Q
--
-- Σ[ (i , j) ∈ P .Tag × Q . Tag] x^(aᵢ Ⓥ bⱼ)
infixr 8 _Ⓥ_
_Ⓥ_ : Poly → Poly → Poly
(P Ⓥ Q) .Tag = P .Tag × Q .Tag
(P Ⓥ Q) .Args = λ where
  (ptag , qtag) →  Args P ptag ⊎ (Args P ptag × Args Q qtag) ⊎ Args Q qtag

--------------------------------------------------------------------------------

-- | P ∨ Q
--
-- P ∨ Q ≔ P + (P ⊗ Q) + Q
infixr 5 _∨_
_∨_ :  Poly → Poly → Poly
P ∨ Q = P + (P ⊗ Q) + Q

-- | _∨_ This Inclusion
This : ∀{P Q : Poly} → P ⇒ (P ∨ Q)
This .map-tag ptag = inj₁ ptag
This .map-args ptag = id

-- | _∨_ That Inclusion
That : ∀{P Q : Poly} → Q ⇒ (P ∨ Q)
That .map-tag qtag = inj₂ (inj₂ qtag)
That .map-args qtag = id

-- | _∨_ These Inclusion
These : ∀{P Q : Poly} → (P ⊗ Q) ⇒ (P ∨ Q)
These .map-tag tags = inj₂ (inj₁ tags)
These .map-args tags = id

-- | _∨_ Eliminator
theseₚ : ∀{P Q R : Poly} → P ⇒ R → Q ⇒ R → (P ⊗ Q) ⇒ R → (P ∨ Q) ⇒ R
(theseₚ p⇒r q⇒r pq⇒r) .map-tag  (inj₁ ptag) = map-tag p⇒r ptag
(theseₚ p⇒r q⇒r pq⇒r) .map-tag (inj₂ (inj₁ tags)) = map-tag pq⇒r tags
(theseₚ p⇒r q⇒r pq⇒r) .map-tag (inj₂ (inj₂ qtag)) = map-tag q⇒r qtag
(theseₚ p⇒r q⇒r pq⇒r) .map-args (inj₁ ptag) args = map-args p⇒r ptag args
(theseₚ p⇒r q⇒r pq⇒r) .map-args (inj₂ (inj₁ tags)) args = map-args pq⇒r tags args
(theseₚ p⇒r q⇒r pq⇒r) .map-args (inj₂ (inj₂ qtag)) args = map-args q⇒r qtag args
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

_+⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P + R ⇒ Q + Z
(p⇒q +⇒ r⇒z) .map-tag (inj₁ ptag) = inj₁ (map-tag p⇒q ptag)
(p⇒q +⇒ r⇒z) .map-tag (inj₂ rtag) = inj₂ (map-tag r⇒z rtag)
(p⇒q +⇒ r⇒z) .map-args (inj₁ ptag) = map-args p⇒q ptag
(p⇒q +⇒ r⇒z) .map-args (inj₂ rtag) = map-args r⇒z rtag

_◁⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P ◁ R ⇒ Q ◁ Z
(p⇒q ◁⇒ r⇒z) .map-tag (ptag , parg→rtag) = (map-tag p⇒q ptag) , λ qargs → map-tag r⇒z (parg→rtag (map-args p⇒q ptag qargs))
(p⇒q ◁⇒ r⇒z) .map-args (ptag , parg→rtag) (qargs , zargs) = map-args p⇒q ptag qargs , map-args r⇒z (parg→rtag (map-args p⇒q ptag qargs)) zargs

_×ₚ⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P ×ₚ R ⇒ Q ×ₚ Z
(p⇒q ×ₚ⇒ r⇒z) .map-tag (ptag , rtag) = (map-tag p⇒q ptag) , (map-tag r⇒z rtag)
(p⇒q ×ₚ⇒ r⇒z) .map-args (ptag , rtag) (inj₁ qargs) = inj₁ (map-args p⇒q ptag qargs)
(p⇒q ×ₚ⇒ r⇒z) .map-args (ptag , rtag) (inj₂ zargs) = inj₂ (map-args r⇒z rtag zargs)

_⊗⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P ⊗ R ⇒ Q ⊗ Z
(p⇒q ⊗⇒ r⇒z) .map-tag (ptag , rtag) =(map-tag p⇒q ptag) , (map-tag r⇒z rtag)
(p⇒q ⊗⇒ r⇒z) .map-args (ptag , rtag) (qargs , zargs) = (map-args p⇒q ptag qargs) , (map-args r⇒z rtag zargs)

_Ⓥ⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P Ⓥ  R ⇒ Q Ⓥ Z
(p⇒q Ⓥ⇒ r⇒z) .map-tag (ptag , rtag) = map-tag p⇒q ptag , map-tag r⇒z rtag
(p⇒q Ⓥ⇒ r⇒z) .map-args (ptag , rtag) (inj₁ qargs) = inj₁ (map-args p⇒q ptag qargs)
(p⇒q Ⓥ⇒ r⇒z) .map-args (ptag , rtag) (inj₂ (inj₁ (qargs , zargs))) = inj₂ (inj₁ ((map-args p⇒q ptag qargs) , (map-args r⇒z rtag zargs)))
(p⇒q Ⓥ⇒ r⇒z) .map-args (ptag , rtag) (inj₂ (inj₂ zargs)) = inj₂ (inj₂ (map-args r⇒z rtag zargs))

_∨⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P ∨ R ⇒ Q ∨ Z
(p⇒q ∨⇒ r⇒z) .map-tag (inj₁ ptag) = inj₁ (map-tag p⇒q ptag)
(p⇒q ∨⇒ r⇒z) .map-tag (inj₂ (inj₁ (ptag , rtag))) = inj₂ (inj₁ ((map-tag p⇒q ptag) , (map-tag r⇒z rtag)))
(p⇒q ∨⇒ r⇒z) .map-tag (inj₂ (inj₂ rtag)) = inj₂ (inj₂ (map-tag r⇒z rtag))
(p⇒q ∨⇒ r⇒z) .map-args (inj₁ ptag) args = map-args p⇒q ptag args
(p⇒q ∨⇒ r⇒z) .map-args (inj₂ (inj₁ (ptag , rtag))) (qargs , zargs) = (map-args p⇒q ptag qargs) , map-args r⇒z rtag zargs
(p⇒q ∨⇒ r⇒z) .map-args (inj₂ (inj₂ rtag)) args = map-args r⇒z rtag args
