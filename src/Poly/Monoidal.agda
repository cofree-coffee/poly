-- | Monoidal Structures on Poly
module Poly.Monoidal where

--------------------------------------------------------------------------------

open import Data.Unit
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Poly
open import Poly.Isomorphism
open import Poly.Monoidal.Coproduct
open import Poly.Monoidal.Compose
open import Poly.Monoidal.Product
open import Poly.Monoidal.Tensor
open import Poly.Monoidal.Or
open import Poly.Monoidal.Other

--------------------------------------------------------------------------------

[_,_] : Poly → Poly → Poly
Base [ P , Q ] = P ⇒ Q
Fiber [ P , Q ] = λ f → Σ[ p ∈ P .Base ] Q .Fiber (f .map-base p)

⊗-to-hom : ∀{ P Q R : Poly} → P ⊗ Q ⇒ R → P ⇒ [ Q , R ]
map-base (map-base (⊗-to-hom p⊗q) p-base) q-base = p⊗q .map-base (p-base , q-base)
map-fiber (map-base (⊗-to-hom p⊗q) p-base) q-base r-fiber = proj₂ (p⊗q .map-fiber (p-base , q-base) r-fiber) 
map-fiber (⊗-to-hom p⊗q) p-base (q-base , r-fiber) = proj₁ (p⊗q .map-fiber (p-base , q-base) r-fiber)

hom-to-⊗ : ∀{ P Q R : Poly} → P ⇒ [ Q , R ] → P ⊗ Q ⇒ R
map-base (hom-to-⊗ p[qr]) (p-base , q-base) = (p[qr] .map-base p-base) .map-base q-base
map-fiber (hom-to-⊗ p[qr]) (p-base , q-base) r-fiber =
  let q-fib = p[qr] .map-base p-base .map-fiber q-base r-fiber
  in p[qr] .map-fiber p-base (q-base , r-fiber) , q-fib

λₚ : ∀{ Γ P Q : Poly } → Γ ⊗ P ⇒ Q → Γ ⇒ [ P , Q ]
map-base (map-base (λₚ f) γ-base) = λ p-base → f .map-base (γ-base , p-base)
map-fiber (map-base (λₚ f) γ-base) = λ p-base q-fib →  proj₂ (f .map-fiber (γ-base , p-base) q-fib)
map-fiber (λₚ f) γ-base (p-base , q-fib) = proj₁ (f .map-fiber (γ-base , p-base) q-fib)

apₚ : ∀{ Γ P Q : Poly } → Γ ⇒ [ P , Q ] ⊗ P → Γ ⇒ Q
map-base (apₚ f) γ-base = let (g , p-base) = f .map-base γ-base in  g .map-base p-base
map-fiber (apₚ f) γ-base q-fib =
  f .map-fiber γ-base ((proj₂ (f .map-base γ-base) , q-fib) ,
    let (g , p-base) = (f .map-base γ-base)
    in g .map-fiber p-base q-fib)

eval : ∀ {P Q : Poly} → P ⊗ [ P , Q ] ⇒ Q
eval = ⊗-swap ⨟ₚ (apₚ idₚ)

hom-to-𝕐
  : ∀ {A B : Set}
  → [ monomial A ⊤ , monomial B ⊤ ] ⇒ [ monomial A B , 𝕐 ]
map-base hom-to-𝕐 Ay⇒By = record { map-base = λ a → tt ; map-fiber = λ a y-fib → Ay⇒By .map-base a }
map-fiber hom-to-𝕐 Ay⇒By (a , y-fib) = a , tt

duoidality : ∀{P1 P2 Q1 Q2 : Poly} → (P1 ◁ P2) ⊗ (Q1 ◁ Q2) ⇒ (P1 ⊗ Q1) ◁ (P2 ⊗ Q2)
duoidality .map-base ((p1 , p2) , q1 , q2) = (p1 , q1) , λ { (fst , snd) → p2 fst , q2 snd }
duoidality .map-fiber ((p1 , p2) , q1 , q2) ((i1 , j1) , i2 , j2) = (i1 , i2) , j1 , j2

indep : ∀ {P Q : Poly} → P ⊗ Q ⇒ P ◁ Q
indep {P} {Q} = (◁-unit-r .fwd ⊗⇒ ◁-unit-l .fwd) ⨟ₚ duoidality ⨟ₚ (⊗-unit-r .fwd ◁⇒ ⊗-unit-l .fwd)

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

-- comonoid-pow : ∀{P : Poly} → (n : ℕ) → (ProposedComonoid P) → P ⇒ pow-◁ n P
-- comonoid-pow {P} zero comonoid = ProposedComonoid.e comonoid 
-- comonoid-pow {P} (suc zero) comonoid = ◁-id-intro P
-- comonoid-pow {P} (suc (suc n)) comonoid = (comonoid-pow (suc n) comonoid) ⨟ₚ {!!}
