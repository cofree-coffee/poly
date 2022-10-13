module Poly.SetFunctor where

open import Level using (Level; suc; _⊔_)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Sum.Base using (_⊎_)
open import Function.Base using (id ; _∘_)
open import Effect.Functor
open import Relation.Binary

-- * Natural transformations and isomorphisms

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

private variable
  a b c : Level

≃-∘₁ : {F : Set b → Set c} → ⦃ RawFunctor F ⦄ → (F ∘_) Preserves (_≃_ {a = a}) ⟶ _≃_
≃-∘₁ ⦃ RawF ⦄ (to , from) = (to <$>_) , (from <$>_)
  where open RawFunctor RawF

≃-∘₂ : {F : Set a → Set b} → (_∘ F) Preserves _≃_ ⟶ (_≃_ {b = c})
≃-∘₂ (to , from) = to , from

-- * Operations

infixl 6 _+₁_
infixl 7 _×₁_

-- | Sum of two functors (aka. coproduct).
_+₁_ : (F G : Set a → Set b) → Set a → Set b
(F +₁ G) A = F A ⊎ G A

-- | Cartesian product of two functors.
_×₁_ : (F G : Set a → Set b) → Set a → Set b
(F ×₁ G) A = F A × G A

-- | Sum of functors.
Sum₁ : (I : Set a) → (I → Set b → Set (a ⊔ c)) → Set b → Set (a ⊔ c)
Sum₁ I F A = ∃[ i ] F i A

-- | Product of functors.
Product₁ : (I : Set a) → (I → Set b → Set (a ⊔ c)) → Set b → Set (a ⊔ c)
Product₁ I F A = (i : I) → F i A

infix 2 Sum₁ Product₁
syntax Sum₁ I (λ i → F) = Σ₁[ i ∈ I ] F
syntax Product₁ I (λ i → F) = Π₁[ i ∈ I ] F

-- | Day convolution.
day : (F G : Set a → Set (suc a ⊔ b)) → Set a → Set (suc a ⊔ b)
day F G A = ∃[ B ] ∃[ C ] (B → C → A) × F B × G C

-- | Closure of Day convolution.
exp : (F G : Set a → Set (suc a ⊔ b)) → Set a → Set (suc a ⊔ b)
exp F G A = ∀ {B C} → (A → B → C) → F B → G C
