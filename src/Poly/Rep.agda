{-# OPTIONS --type-in-type --allow-unsolved-metas #-}
-- | The Co-Product of Representables Encoding of Poly
module Poly.Rep where

--------------------------------------------------------------------------------

open import Data.Fin using (Fin; suc; zero)
open import Data.Product using (Σ-syntax)
open import Poly
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------

infix 0 _≃_
record _≃_ (F G : (Set → Set)) : Set where
  field
    to   : ∀ {X : Set} → F X → G X
    from : ∀ {X : Set} → G X → F X
    from∘to : ∀ {X : Set} (x : F X) → from (to x) ≡ x
    to∘from : ∀ {X : Set} (y : G X) → to (from y) ≡ y
open _≃_

--------------------------------------------------------------------------------

record IsRepresentable (F : Set → Set) : Set where
  constructor proveIsRepr
  field
    Index : Set
    Iso : F ≃ λ X → (Index → X)

trivial : ∀ I → IsRepresentable (λ X → (I → X))
(trivial I) .IsRepresentable.Index = I
(trivial I) .IsRepresentable.Iso =
  record
    { to = λ f → f
    ; from = λ f → f
    ; from∘to = λ x → refl
    ; to∘from = λ y → refl
    }

--------------------------------------------------------------------------------

record Poly-Rep : Set where
  no-eta-equality
  constructor poly
  field
    Tag : Set
    Functors : Tag → Set → Set
    IsRepr : ∀ (tag : Tag) → IsRepresentable (Functors tag)

open Poly-Rep public

private variable
  A B C D S T I O : Set
  P Q R : Poly-Rep

intoFunctor : Poly-Rep → (Set → Set)
intoFunctor cor = λ X → Σ[ tag ∈ cor .Tag ] cor .Functors tag X

--------------------------------------------------------------------------------

identityₚ : Poly-Rep
Tag identityₚ = Fin 1
Functors identityₚ zero X = Fin 1 → X
IsRepr identityₚ zero =
  proveIsRepr (Fin 1)
    (record
      { to = λ f fin₀ → f fin₀
      ; from = λ f → f
      ; from∘to = λ f → refl
      ; to∘from = λ f → refl
      })

Identity : Set → Set
Identity = intoFunctor identityₚ

-- TODO:
maybeₚ : Poly-Rep
Tag maybeₚ = Fin 2
Functors maybeₚ zero X = Fin 0 → X
Functors maybeₚ (suc zero) X = Fin 1 → X
IsRepr maybeₚ zero = proveIsRepr (Fin 0) (record { to = λ f () ; from = λ g () ; from∘to = λ f → {!!} ; to∘from = λ y → {!!} })
IsRepr maybeₚ (suc tag) = proveIsRepr (Fin 1) (record { to = λ F tt → {!!} ; from = λ f → {!!} ; from∘to = {!!} ; to∘from = {!!} })
