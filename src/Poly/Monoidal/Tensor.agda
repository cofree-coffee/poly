{-# OPTIONS --type-in-type #-}
module Poly.Monoidal.Tensor where

--------------------------------------------------------------------------------

open import Data.Unit
open import Data.Product using (_×_; _,_)
open import Function using (id)
open import Poly
open import Poly.Isomorphism
open import Poly.Comonoid
open import Poly.Monoid
open import Poly.SetFunctor

open _≃_

--------------------------------------------------------------------------------

-- | P ⊗ Q
-- Also called the Parallel Product of two Polynomials
--
-- P ⊗ Q ≔ ∑[ i ∈ P .Base × Q .Base ] y^(aᵢ × bⱼ)
infixr 7 _⊗_
_⊗_ : Poly → Poly → Poly
(P ⊗ Q) .Base  = Base P × Base Q
(P ⊗ Q) .Fiber (ptag , qtag) = Fiber P ptag × Fiber Q qtag

-- | Functorial Action of _⊗_
_⊗⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P ⊗ R ⇒ Q ⊗ Z
(p⇒q ⊗⇒ r⇒z) .map-base (ptag , rtag) = (map-base p⇒q ptag) , (map-base r⇒z rtag)
(p⇒q ⊗⇒ r⇒z) .map-fiber (ptag , rtag) (qargs , zargs) = (map-fiber p⇒q ptag qargs) , (map-fiber r⇒z rtag zargs)

⊗-swap : ∀{P Q : Poly} → P ⊗ Q ⇒ Q ⊗ P
⊗-swap .map-base (ptag , qtag) = qtag , ptag
⊗-swap .map-fiber tag (qargs , pargs) = pargs , qargs

⊗-split-l : ∀{P : Poly} → P ⇒ P ⊗ P
⊗-split-l .map-base ptag =  ptag , ptag
⊗-split-l .map-fiber ptag (f , g) = f

⊗-split-r : ∀{P : Poly} → P ⇒ P ⊗ P
⊗-split-r .map-base ptag =  ptag , ptag
⊗-split-r .map-fiber ptag (f , g) = g

⊗-unit-l : ∀{P : Poly} → ProposedIso (𝕐 ⊗ P) P
map-base (fwd ⊗-unit-l) (tt , p-base) = p-base
map-fiber (fwd ⊗-unit-l) (tt , p-base) p-fiber = tt , p-fiber
map-base (bwd ⊗-unit-l) p-base = tt , p-base
map-fiber (bwd ⊗-unit-l) p-base (tt , p-fib) = p-fib

⊗-unit-r : ∀{P : Poly} → ProposedIso (P ⊗ 𝕐) P
fwd ⊗-unit-r = ⊗-swap ⨟ₚ ⊗-unit-l .fwd
bwd ⊗-unit-r = ⊗-unit-l .bwd ⨟ₚ ⊗-swap

⊗-assoc : ∀{P Q R : Poly} → ProposedIso (P ⊗ (Q ⊗ R)) ((P ⊗ Q) ⊗ R)
map-base (fwd ⊗-assoc) (p-base , q-base , r-base) = (p-base , q-base) , r-base
map-fiber (fwd ⊗-assoc) _ ((p-fib , q-fib) , r-fib) = p-fib , (q-fib , r-fib)
map-base (bwd ⊗-assoc) ((p-base , q-base) , r-base) = (p-base , q-base , r-base)
map-fiber (bwd ⊗-assoc) _ (p-fib , (q-fib , r-fib)) = ((p-fib , q-fib) , r-fib)

-- | The parallel product represents day convolution.
⊗-⟦⟧ : ∀{P Q : Poly} → ⟦ P ⊗ Q ⟧ ≃ day ⟦ P ⟧ ⟦ Q ⟧
⊗-⟦⟧ {P = P} {Q = Q} .to ((ptag , qtag) , f) = P .Fiber ptag , Q .Fiber qtag , (λ pargs qargs → f (pargs , qargs)) , (ptag , id) , (qtag , id)
⊗-⟦⟧ .from (B , C , f , (ptag , b) , (qtag , c)) = (ptag , qtag) , λ (pargs , qargs) → f (b pargs) (c qargs)
