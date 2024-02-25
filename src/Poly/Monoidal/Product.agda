{-# OPTIONS --type-in-type #-}
module Poly.Monoidal.Product where

--------------------------------------------------------------------------------

open import Data.Unit
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; [_,_]; inj₁; inj₂)
open import Function using (_∘_)
open import Poly
open import Poly.Comonoid
open import Poly.SetFunctor

open _≃_

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

_×ₚ⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P ×ₚ R ⇒ Q ×ₚ Z
(p⇒q ×ₚ⇒ r⇒z) .map-base (ptag , rtag) = (map-base p⇒q ptag) , (map-base r⇒z rtag)
(p⇒q ×ₚ⇒ r⇒z) .map-fiber (ptag , rtag) (inj₁ qargs) = inj₁ (map-fiber p⇒q ptag qargs)
(p⇒q ×ₚ⇒ r⇒z) .map-fiber (ptag , rtag) (inj₂ zargs) = inj₂ (map-fiber r⇒z rtag zargs)

×-monoid : ∀{P : Poly} → ProposedComonoid (_×ₚ_) 𝟙
ProposedComonoid.P (×-monoid {P}) = P
map-base (ProposedComonoid.e ×-monoid) p-base = tt
map-fiber (ProposedComonoid.e ×-monoid) tag ()
map-base (ProposedComonoid._⋆_ ×-monoid) p-base = p-base , p-base
map-fiber (ProposedComonoid._⋆_ ×-monoid) tag (inj₁ p-fib) = p-fib
map-fiber (ProposedComonoid._⋆_ ×-monoid) tag (inj₂ p-fib) = p-fib

-- | _×ₚ_ fst eliminator
×ₚ-fst : ∀{P Q : Poly} → (P ×ₚ Q) ⇒ P
×ₚ-fst .map-base (ptag , qtag) = ptag
×ₚ-fst .map-fiber (ptag , qtag) pargs = inj₁ pargs

-- | _×ₚ_ snd eliminator
×ₚ-snd : ∀{P Q : Poly} → (P ×ₚ Q) ⇒ Q
×ₚ-snd .map-base (ptag , qtag) = qtag
×ₚ-snd .map-fiber (ptag , qtag) qargs = inj₂ qargs

×ₚ-swap : ∀{P Q : Poly} → (P ×ₚ Q) ⇒ (Q ×ₚ P)
×ₚ-swap .map-base (ptag , qtag) = qtag , ptag
×ₚ-swap .map-fiber (ptag , qtag) (inj₁ qargs) = inj₂ qargs
×ₚ-swap .map-fiber (ptag , qtag) (inj₂ pargs) = inj₁ pargs

×ₚ-dupe : ∀{P : Poly} → P ⇒ P ×ₚ P
×ₚ-dupe .map-base ptag =  ptag , ptag
×ₚ-dupe .map-fiber ptag (inj₁ pargs) = pargs
×ₚ-dupe .map-fiber ptag (inj₂ pargs) = pargs

_&&&_ : ∀{P Q R : Poly} → R ⇒ P → R ⇒ Q → R ⇒ (P ×ₚ Q)
(f &&& g) .map-base rtag =  map-base f rtag , map-base g rtag
(f &&& g) .map-fiber rtag (inj₁ pargs) = map-fiber f rtag pargs
(f &&& g) .map-fiber rtag (inj₂ qargs) = map-fiber g rtag qargs

×ₚ-⟦⟧ : ∀{P Q : Poly} → ⟦ P ×ₚ Q ⟧ ≃ ⟦ P ⟧ ×₁ ⟦ Q ⟧
×ₚ-⟦⟧ .to ((ptag , qtag) , f) = (ptag , λ pargs → f (inj₁ pargs)) , (qtag , λ qargs → f (inj₂ qargs))
×ₚ-⟦⟧ .from ((ptag , f) , (qtag , g)) = (ptag , qtag) , [ f , g ]

-- | p ×ₚ q can be recovered as Product Bool (if _ then q else p)
Product : (I : Set) → (I → Poly) → Poly
(Product I f) .Base = ∀ (i : I) → f i .Base
(Product I f) .Fiber tags = Σ[ i ∈ I ] (f i) .Fiber (tags i)

infix 2 Product
syntax Product I (λ i → P) = Πₚ[ i ∈ I ] P

⟦⟧-Product : {I : Set} {P : I → Poly} → ⟦ Πₚ[ i ∈ I ] P i ⟧ ≃ (Π₁[ i ∈ I ] ⟦ P i ⟧)
⟦⟧-Product .to (ptag , f) i = ptag i , λ pargs → f (i , pargs)
⟦⟧-Product .from f = proj₁ ∘ f , λ (i , pargs) → proj₂ (f i) pargs
