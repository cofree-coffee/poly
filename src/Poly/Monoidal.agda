{-# OPTIONS --type-in-type #-}
-- | Monoidal Structures on Poly
module Poly.Monoidal where

--------------------------------------------------------------------------------

open import Data.Unit
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Poly
open import Poly.Comonoid
open import Poly.Monoidal.Coproduct
open import Poly.Monoidal.Compose
open import Poly.Monoidal.Product
open import Poly.Monoidal.Tensor
open import Poly.Monoidal.Or
open import Poly.Monoidal.Other

--------------------------------------------------------------------------------

duoidality : ∀{P1 P2 Q1 Q2 : Poly} → (P1 ◁ P2) ⊗ (Q1 ◁ Q2) ⇒ (P1 ⊗ Q1) ◁ (P2 ⊗ Q2)
duoidality .map-base ((p1 , p2) , q1 , q2) = (p1 , q1) , λ { (fst , snd) → p2 fst , q2 snd }
duoidality .map-fiber ((p1 , p2) , q1 , q2) ((i1 , j1) , i2 , j2) = (i1 , i2) , j1 , j2

⊗-◁-lemma : ∀{P Q : Poly} → P ⊗ Q ⇒ (P ◁ 𝕐) ⊗ (𝕐 ◁ Q)
⊗-◁-lemma .map-base (pbase , qbase) = (pbase , (λ x → tt)) , tt , (λ x → qbase)
⊗-◁-lemma .map-fiber (pbase , qbase) ((p-fib , y-fib) , y-fib , q-fib) = p-fib , q-fib

-- TODO: implement via duoidality
indep : ∀ {P Q : Poly} → P ⊗ Q ⇒ P ◁ Q
indep .map-base (pbase , qbase) = pbase , λ x → qbase
indep .map-fiber (pbase , qbase) (p-fib , q-fib) = p-fib , q-fib

⊗-Day-× : ∀{P1 P2 Q1 Q2 : Poly} → (P1 ◁ P2) ×ₚ (Q1 ◁ Q2) ⇒ (P1 ⊗ Q1) ◁ (P2 ×ₚ Q2)
⊗-Day-× .map-base ((p1-base , f) , q1-base , g) = (p1-base , q1-base) , (λ where (p1-fib , q1-fib) → (f p1-fib) , (g q1-fib))
⊗-Day-× .map-fiber ((p1-base , f) , q1-base , g) ((p1-fib , q1-fib) , inj₁ p2-fib) = inj₁ (p1-fib , p2-fib)
⊗-Day-× .map-fiber ((p1-base , f) , q1-base , g) ((p1-fib , q1-fib) , inj₂ q2-fib) = inj₂ (q1-fib , q2-fib)

×-Day-+ : ∀{P1 P2 Q1 Q2 : Poly} → (P1 ◁ P2) ×ₚ (Q1 ◁ Q2) ⇒ (P1 ×ₚ Q1) ◁ (P2 + Q2)
×-Day-+ .map-base ((p1-base , f) , q1-base , g) = (p1-base , q1-base) , λ where
  (inj₁ p1-fib) → inj₁ (f p1-fib)
  (inj₂ q1-fib) → inj₂ (g q1-fib)
×-Day-+ .map-fiber ((p1-base , f) , q1-base , g) (inj₁ p1-fib , p2-fib) = inj₁ (p1-fib , p2-fib)
×-Day-+ .map-fiber ((p1-base , f) , q1-base , g) (inj₂ q1-fib , q2-fib) = inj₂ (q1-fib , q2-fib)

Store : Set → Poly
Store S = monomial S S

store-p-comonoid : ∀{S : Set} → ProposedComonoid (_◁_) 𝕐
store-p-comonoid {S} .ProposedComonoid.P = (Store S)
store-p-comonoid .ProposedComonoid.e = poly-map (λ x → tt) λ s _ → s
store-p-comonoid .ProposedComonoid._⋆_ = poly-map (λ s → s , λ s' → s') λ where
  tag (fst , snd) → snd

-- comonoid-pow : ∀{P : Poly} → (n : ℕ) → (ProposedComonoid P) → P ⇒ pow-◁ n P
-- comonoid-pow {P} zero comonoid = ProposedComonoid.e comonoid 
-- comonoid-pow {P} (suc zero) comonoid = ◁-id-intro P
-- comonoid-pow {P} (suc (suc n)) comonoid = (comonoid-pow (suc n) comonoid) ⨟ₚ {!!}
