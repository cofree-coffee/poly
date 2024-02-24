{-# OPTIONS --type-in-type #-}
module Poly.Monoidal.Compose where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Unit
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Function using (_∘_; id)
open import Poly
open import Poly.SetFunctor
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open _≃_

--------------------------------------------------------------------------------

-- | P ◁ Q
-- Composition of Polyonomial Functors
--
-- ⟦ P ◁ Q ⟧ ≡ ⟦ P ⟧ ∘ ⟦ Q ⟧
-- Σ ? Π ?   ≡ Σ Π (Σ Π)
--
-- 𝟙y^𝟚 ◁ X ≡ 𝟙X^𝟚
_◁_ : Poly → Poly → Poly
(P ◁ Q) .Base = Σ[ ptag ∈ P .Base ] (P .Fiber ptag → Q .Base) 
(P ◁ Q) .Fiber  (ptag , f) =  Σ[ pargs ∈ P .Fiber ptag ] Q .Fiber (f pargs)

_◁⇒_ : ∀{P Q R Z : Poly} → P ⇒ Q → R ⇒ Z → P ◁ R ⇒ Q ◁ Z
(p⇒q ◁⇒ r⇒z) .map-base (ptag , parg→rtag) = (map-base p⇒q ptag) , λ qargs → map-base r⇒z (parg→rtag (map-fiber p⇒q ptag qargs))
(p⇒q ◁⇒ r⇒z) .map-fiber (ptag , parg→rtag) (qargs , zargs) = map-fiber p⇒q ptag qargs , map-fiber r⇒z (parg→rtag (map-fiber p⇒q ptag qargs)) zargs


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
