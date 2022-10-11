{-# OPTIONS --type-in-type #-}
module Poly.Profunctor where

--------------------------------------------------------------------------------

open import Data.Product 
open import Data.Sum
open import Poly
open import Poly.Monoidal

--------------------------------------------------------------------------------

private variable
  A B C D S T I O : Set
  P Q R Z : Poly

--------------------------------------------------------------------------------

-- | _⇒_ is a Profunctor
dimap-⇒ : Q ⇒ R → Z ⇒ P → P ⇒ Q → Z ⇒ R
dimap-⇒ q⇒r z⇒p p⇒q = z⇒p ⨟ (p⇒q ⨟ q⇒r)

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

-- unfirst : (P ×ₚ R) ⇒ (Q ×ₚ R) → P ⇒ Q
-- (unfirst pr⇒qr) .map-tag tag = map-tag (pr⇒qr ⨟ fstₚ) (tag , {!!} )
-- (unfirst pr⇒qr) .map-args = {!!}

-- unsecond : (R ⊗ P) ⇒ (R ⊗ Q) → P ⇒ Q
-- (unsecond rp⇒rq) .map-tag tag = {!!}
-- (unsecond rp⇒rq) .map-args = {!!}