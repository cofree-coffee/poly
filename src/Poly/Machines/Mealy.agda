{-# OPTIONS --type-in-type #-}
module Poly.Machines.Mealy where

--------------------------------------------------------------------------------

open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Poly

--------------------------------------------------------------------------------

-- | Mealy Machine:
-- 
-- S × I → S
-- S × I → O
--
-- | SI · xˢ → O · x¹
Mealy : Set → Set → Set → Set
Mealy S I O = monomial (S × I) S ⇒ monomial O ⊤

mealy : ∀{S I O : Set} → (S × I → (S × O)) → Mealy S I O
mealy f .map-base = proj₂ ∘ f
mealy f .map-fiber tag = λ _ → (proj₁ ∘ f) tag

-- | Evaluate one step of a Mealy Machine with a given input @I@ and
-- | state @S@.
step-mealy : ∀{S I O : Set} →  I → S → Mealy S I O → (O × S)
step-mealy i s bot = bot .map-base ( s , i) , bot .map-fiber (s , i) tt

-- | Turn the crank on a Mealy Machine with a list of inputs @I@.
process-mealy : ∀{S I O : Set} →  S → List I → Mealy S I O → List O × S
process-mealy s [] bot = [] , s 
process-mealy s (i ∷ is) bot =
  let
    (o , s') = step-mealy i s bot
    (os , s'') = process-mealy s' is bot
  in  o ∷ os , s''

mealy-+ : ∀{S₁ S₂ I₁ I₂ O₁ O₂ : Set} → Mealy S₁ I₁ O₁ → Mealy S₂ I₂ O₂ → Mealy (S₁ × S₂) (I₁ ⊎ I₂) (O₁ ⊎ O₂)
mealy-+ m n .map-base ((s₁ , s₂) , inj₁ i₁) = inj₁ (map-base m (s₁ , i₁))
mealy-+ m n .map-base ((s₁ , s₂) , inj₂ i₂) = inj₂ (map-base n (s₂ , i₂))
mealy-+ m n .map-fiber ((s₁ , s₂) , inj₁ i₁) tt = (map-fiber m (s₁ , i₁) tt) , s₂ 
mealy-+ m n .map-fiber ((s₁ , s₂) , inj₂ i₂) tt = s₁ , (map-fiber n (s₂ , i₂) tt)

mealy-× : ∀{S₁ S₂ I₁ I₂ O₁ O₂ : Set} → Mealy S₁ I₁ O₁ → Mealy S₂ I₂ O₂ → Mealy (S₁ × S₂) (I₁ × I₂) (O₁ × O₂)
mealy-× m n .map-base ((s₁ , s₂) , i₁ , i₂) = (map-base m (s₁ , i₁)) , (map-base n (s₂ , i₂))
mealy-× m n .map-fiber ((s₁ , s₂) , i₁ , i₂) tt = (map-fiber m (s₁ , i₁) tt) , (map-fiber n (s₂ , i₂) tt)
