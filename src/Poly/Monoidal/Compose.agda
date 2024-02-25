{-# OPTIONS --type-in-type #-}
module Poly.Monoidal.Compose where

--------------------------------------------------------------------------------

open import Data.Nat hiding (_+_)
open import Data.Fin hiding (_+_)
open import Data.Unit
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Sum
open import Function using (_∘_; id)
open import Poly
open import Poly.Monoidal.Coproduct
open import Poly.Monoidal.Product
open import Poly.Isomorphism
open import Poly.SetFunctor
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open _≃_

--------------------------------------------------------------------------------

-- | P ◁ Q
-- Composition of Polyonomial Functors
--
-- Σ[i : p(1)] Π[d : p[i]] Σ[j : q(i)] Π[e :q[j]] y
--
-- 𝟙y^𝟚 ◁ X ≡ 𝟙X^𝟚
_◁_ : Poly → Poly → Poly
(P ◁ Q) .Base = Σ[ ptag ∈ P .Base ] (P .Fiber ptag → Q .Base) 
(P ◁ Q) .Fiber  (pbase , f) =  Σ[ pfib ∈ P .Fiber pbase ] Q .Fiber (f pfib)

_◁⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P ◁ R ⇒ Q ◁ Z
(p⇒q ◁⇒ r⇒z) .map-base (ptag , parg→rtag) = (map-base p⇒q ptag) , λ qargs → map-base r⇒z (parg→rtag (map-fiber p⇒q ptag qargs))
(p⇒q ◁⇒ r⇒z) .map-fiber (ptag , parg→rtag) (qargs , zargs) = map-fiber p⇒q ptag qargs , map-fiber r⇒z (parg→rtag (map-fiber p⇒q ptag qargs)) zargs

◁-split-l : {P : Poly} → P ⇒ P ◁ P
◁-split-l .map-base pbase = pbase , λ f → pbase
◁-split-l .map-fiber pbase (pfib₁ , pfib₂) = pfib₁

◁-split-r : {P : Poly} → P ⇒ P ◁ P
◁-split-r .map-base pbase = pbase , λ f → pbase
◁-split-r .map-fiber pbase (pfib₁ , pfib₂) = pfib₂

◁-unit-l : {P : Poly} → ProposedIso P (𝕐 ◁ P)
map-base (fwd ◁-unit-l) p-base = tt , λ _ → p-base
map-fiber (fwd ◁-unit-l) p-base = proj₂
map-base (bwd ◁-unit-l) (tt , f) = f tt
map-fiber (bwd ◁-unit-l) p-base p-fib = tt , p-fib

◁-unit-r : {P : Poly} → ProposedIso P (P ◁ 𝕐)
map-base (fwd ◁-unit-r) p-base = p-base , λ _ → tt
map-fiber (fwd ◁-unit-r) p-base = proj₁ 
map-base (bwd ◁-unit-r) = proj₁
map-fiber (bwd ◁-unit-r) p-base p-fib = p-fib , tt

+-◁-iso : ∀{P Q R : Poly} → ProposedIso ((P + Q) ◁ R) ((P ◁ R) + (Q ◁ R))
map-base (fwd +-◁-iso) (inj₁ p-base , f) = inj₁ (p-base , f)
map-base (fwd +-◁-iso) (inj₂ q-base , g) = inj₂ (q-base , g)
map-fiber (fwd +-◁-iso) (inj₁ p-base , f) (p-fib , r-fib) = p-fib , r-fib
map-fiber (fwd +-◁-iso) (inj₂ q-base , g) (q-fib , r-fib) = q-fib , r-fib
map-base (bwd +-◁-iso) (inj₁ (p-base , f)) = (inj₁ p-base) , f
map-base (bwd +-◁-iso) (inj₂ (q-base , g)) = (inj₂ q-base) , g
map-fiber (bwd +-◁-iso) (inj₁ (p-base , f)) (p-fib , r-fib) = p-fib , r-fib
map-fiber (bwd +-◁-iso) (inj₂ (q-base , g)) (q-fib , r-fib) = q-fib , r-fib

×-◁-iso : ∀{P Q R : Poly} → ProposedIso ((P ×ₚ Q) ◁ R) ((P ◁ R) ×ₚ (Q ◁ R))
map-base (fwd ×-◁-iso) ((p-base , q-base) , f) = (p-base , λ p-fib → f (inj₁ p-fib)) , q-base , λ q-fib → f (inj₂ q-fib)
proj₁ (map-fiber (fwd ×-◁-iso) ((p-base , q-base) , f) (inj₁ (p-fib , r-fib))) = inj₁ p-fib
proj₁ (map-fiber (fwd ×-◁-iso) ((p-base , q-base) , f) (inj₂ (q-fib , r-fib))) = inj₂ q-fib
proj₂ (map-fiber (fwd ×-◁-iso) ((p-base , q-base) , g) (inj₁ (p-fib , r-fib))) = r-fib
proj₂ (map-fiber (fwd ×-◁-iso) ((p-base , q-base) , g) (inj₂ (q-fib , r-fib))) = r-fib
map-base (bwd ×-◁-iso) ((p-base , f) , q-base , g) = (p-base , q-base) , (λ { (inj₁ p-fib) → f p-fib ; (inj₂ q-fib) → g q-fib })
map-fiber (bwd ×-◁-iso) ((p-base , f) , q-base , g) (inj₁ p-fib , r-fib) = inj₁ (p-fib , r-fib)
map-fiber (bwd ×-◁-iso) ((p-base , f) , q-base , g) (inj₂ q-fib , r-fib) = inj₂ (q-fib , r-fib)

--| Functor composition with _◁_ is well behaved.
⟦⟧-◁ : ∀{P Q : Poly} → ⟦ P ◁ Q ⟧ ≃ ⟦ P ⟧ ∘ ⟦ Q ⟧
⟦⟧-◁ .to ((ptag , qtag) , f) = ptag , λ pargs → qtag pargs , λ qargs → f (pargs , qargs)
⟦⟧-◁ .from (ptag , f) = (ptag , λ pargs → proj₁ (f pargs)) , λ{ (pargs , qargs) → proj₂ (f pargs) qargs }

pow-◁ : ℕ → Poly → Poly
pow-◁ zero p = 𝕐 
pow-◁ (suc n) p = p ◁ pow-◁ n p

pow-◁⇒ : ∀{P Q : Poly} → (n : ℕ) → P ⇒ Q → (pow-◁ n P) ⇒ (pow-◁ n Q)
pow-◁⇒ zero p⇒q = idₚ
pow-◁⇒ (suc n) p⇒q = p⇒q ◁⇒ pow-◁⇒ n p⇒q

◁-assocₗ : ∀{P Q R : Poly} → P ◁ (Q ◁ R) ⇒ (P ◁ Q) ◁ R
◁-assocₗ .map-base (p , qr) = (p , (λ a → let (q , r) = qr a in  q)) ,  λ (x , y) → let (q , r) = qr x in r y
◁-assocₗ .map-fiber (_ , _) ((p , q) , r) = p , (q , r)

◁-assocᵣ : ∀{P Q R : Poly} → (P ◁ Q) ◁ R ⇒ P ◁ (Q ◁ R)
◁-assocᵣ .map-base ((p , q) , r) = p , (λ x → (q x) , (λ y → r (x , y)))
◁-assocᵣ .map-fiber (_ , _) (p , q , r) = (p , q) , r

-- 
x²◁x³ : Poly
x²◁x³ = monomial (Fin 1) (Fin 2) ◁ monomial (Fin 1) (Fin 3)

x²◁x³' : Poly
Base x²◁x³' = Σ[ x²-base ∈ Fin 1 ] (Fin 2 → Fin 1)
Fiber x²◁x³' (x²-base , f) = Σ[ x²-fib ∈ Fin 2 ] (Fin 3)

