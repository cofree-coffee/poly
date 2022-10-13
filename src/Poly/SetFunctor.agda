module Poly.SetFunctor where

open import Level using (Level; suc; _⊔_)
open import Function.Base using (id ; _∘_)
open import Effect.Functor
open import Relation.Binary

module _ {a b : Level} where
  infix 4 _↝_ _≃_

  -- | Natural transformation between functors on Set.
  _↝_ : (Set a → Set b) → (Set a → Set b) → Set (suc a ⊔ b)
  F ↝ G = ∀ {A} → F A → G A

  -- | Natural isomorphism.
  record _≃_ (F G : Set a → Set b) : Set (suc a ⊔ b) where
    constructor _,_
    field
      to : F ↝ G
      from : G ↝ F

  ≃-refl : Reflexive _≃_
  ≃-refl = id , id

  ≃-sym : Symmetric _≃_
  ≃-sym (to , from) = from , to

  ≃-trans : Transitive _≃_
  ≃-trans (to₁ , from₁) (to₂ , from₂) = (to₂ ∘ to₁) , (from₁ ∘ from₂)

≃-∘₁ : ∀ {a b c} {F : Set b → Set c} → ⦃ RawFunctor F ⦄ → (F ∘_) Preserves (_≃_ {a = a}) ⟶ _≃_
≃-∘₁ ⦃ RawF ⦄ (to , from) = (to <$>_) , (from <$>_)
  where open RawFunctor RawF

≃-∘₂ : ∀ {a b c} {F : Set a → Set b} → (_∘ F) Preserves _≃_ ⟶ (_≃_ {b = c})
≃-∘₂ (to , from) = to , from

exp : ∀ {a b} → (F G : Set a → Set (suc a ⊔ b)) → Set a → Set (suc a ⊔ b)
exp F G A = ∀ {B C} → (A → B → C) → F B → G C
