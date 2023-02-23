module Poly.Exponentials where

--------------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (case_of_)
open import Level using (lift)
open import Poly
open import Poly.SetFunctor
open import Poly.Monoidal

open _≃_

--------------------------------------------------------------------------------

private variable
  P Q R : Poly

--------------------------------------------------------------------------------

-- | Adjoint to the cartesian product _×ₚ_.
-- Denoted q^p in the book.
_~>_ : Poly → Poly → Poly
P ~> Q = Product (P .Tag) λ ptag → Q ◁ (constant (P .Args ptag) + 𝐗)

-- | Adjoint to the parallel product _⊗_.
[_~>_] : Poly → Poly → Poly
[ P ~> Q ] = Product (P .Tag) λ ptag → Q ◁ (constant (P .Args ptag) ×ₚ 𝐗)

-- | Does the converse hold?
⟦⟧-~> : ∀ {a b} → exp {a = a} {b = b} ⟦ P ⟧ ⟦ Q ⟧ ↝ ⟦ P ~> Q ⟧ 
⟦⟧-~> f =
  (λ ptag → proj₁ (f (λ x _ → x) (ptag , λ _ → lift tt)) , λ qargs → inj₂ tt) ,
  λ (ptag , qargs , tt) → proj₂ (f (λ x _ → x) (ptag , λ x → lift tt)) qargs

-- | Adjunction _×ₚ Q ⊣ Q ~>_
curry-×ₚ : P ×ₚ Q ⇒ R → P ⇒ (Q ~> R)
curry-×ₚ P×Q⇒R .map-tag ptag qtag = P×Q⇒R .map-tag (ptag , qtag) , λ rargs →
  case P×Q⇒R .map-args (ptag , qtag) rargs of λ where
    (inj₁ pargs) → inj₂ tt
    (inj₂ qargs) → inj₁ qargs
curry-×ₚ P×Q⇒R .map-args ptag (qtag , rargs , f) with P×Q⇒R .map-args (ptag , qtag) rargs
... | inj₁ pargs = pargs
... | inj₂ _ = ⊥-elim f

uncurry-×ₚ : P ⇒ (Q ~> R) → P ×ₚ Q ⇒ R
uncurry-×ₚ P⇒Q~>R .map-tag (ptag , qtag) = proj₁ (P⇒Q~>R .map-tag ptag qtag)
uncurry-×ₚ P⇒Q~>R .map-args (ptag , qtag) rargs
    with proj₂ (P⇒Q~>R .map-tag ptag qtag) rargs | (λ x → P⇒Q~>R .map-args ptag (qtag , rargs , x))
... | inj₁ qargs | _ = inj₂ qargs
... | inj₂ tt    | f = inj₁ (f tt)

apply-×ₚ : (P ~> Q) ×ₚ P ⇒ Q
apply-×ₚ = uncurry-×ₚ idₚ

curry-⊗ : P ⊗ Q ⇒ R → P ⇒ [ Q ~> R ]
curry-⊗ P⊗Q⇒R .map-tag ptag qtag = P⊗Q⇒R .map-tag (ptag , qtag) , λ rargs →
  proj₂ (P⊗Q⇒R .map-args (ptag , qtag) rargs) , tt
curry-⊗ P⊗Q⇒R .map-args ptag (qtag , rargs , inj₂ tt) =
  proj₁ (P⊗Q⇒R .map-args (ptag , qtag) rargs)

uncurry-⊗ : P ⇒ [ Q ~> R ] → P ⊗ Q ⇒ R
uncurry-⊗ P⇒[Q~>R] .map-tag (ptag , qtag) = proj₁ (P⇒[Q~>R] .map-tag ptag qtag)
uncurry-⊗ P⇒[Q~>R] .map-args (ptag , qtag) rargs =
  P⇒[Q~>R] .map-args ptag (qtag , rargs , inj₂ tt) , proj₁ (proj₂ (P⇒[Q~>R] .map-tag ptag qtag) rargs)

apply-⊗ : [ P ~> Q ] ⊗ P ⇒ Q
apply-⊗ = uncurry-⊗ idₚ
