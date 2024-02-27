module Poly.Machines.Moore where

--------------------------------------------------------------------------------

open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_)
open import Poly
open import Poly.Lens
open import Poly.Monoidal.Tensor
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------

-- | Moore Machine:
--
-- S × I → S
-- S → O
--
-- Sxˢ → Oxᴵ
Moore : Set → Set → Set → Set
Moore S I O = monomial S S ⇒ monomial O I

-- | We can build a 'Moore' from an output function and a transition
-- | function.
moore : ∀{S I O : Set} → (S → O) → (S → I → S) → Moore S I O
moore output transition .map-base = output
moore output transition .map-fiber s = transition s

Moore≡Lens : ∀{S I O : Set} → Moore S I O ≡ Lens S S O I
Moore≡Lens = refl

-- | We can then recover the output and transition functions by
-- | eta-expanding around '.map-base' and '.map-fiber'.
disassemble-moore : ∀{S I O : Set} → Moore S I O → (S → O) × (S → I → S)
disassemble-moore m = (λ s → m .map-base s) , λ s i → m .map-fiber s i 

-- | Evaluate one step of a moore machine with a given input @i@ and
-- | state @s@.
step-moore : ∀{S I O : Set} → I → S → Moore S I O → (O × S)
step-moore i s bot = bot .map-base s , bot .map-fiber s i

-- | Turn the crank on a Moore Machine with a list of inputs @I@.
process-moore' : ∀{S I O : Set} →  S → List I → Moore S I O → List O × S
process-moore' s [] bot = [] , s
process-moore' s (i ∷ is) bot =
  let (o , s') = step-moore i s bot 
      (os , s'') = process-moore' s' is bot
  in o ∷ os , s''

-- | Turn the crank on a Moore machine then emit the final state and
-- | the output associated with it.
process-moore : ∀{S I O : Set} →  S → List I → Moore S I O → O × S
process-moore s i bot =
  let (_ , s') = process-moore' s i bot
  in (bot .map-base s') , s'

-- TODO: Broken due to `no-eta-equality` on Poly
-- moore-× : ∀{S₁ S₂ I₁ I₂ O₁ O₂ : Set} → Moore S₁ I₁ O₁ → Moore S₂ I₂ O₂ → Moore (S₁ × S₂) (I₁ × I₂) (O₁ × O₂)
-- moore-× m n = m ⊗⇒ n
