{-# OPTIONS --type-in-type #-}
module Poly.Types.Maybe where

--------------------------------------------------------------------------------

open import Data.Fin using (Fin; suc; zero)
open import Data.Product using (_,_; Σ-syntax)
import Data.Maybe as Agda
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Poly
open import Poly.Monoid
open import Poly.Monoidal.Compose
open import Poly.Monoidal.Coproduct
open import Poly.Monoidal.Product

--------------------------------------------------------------------------------

{-# TERMINATING #-}
freeₚ : Poly → Poly
freeₚ P = 𝕐 + (P ◁ freeₚ P)

iden : Poly
iden = freeₚ 𝟘

_ : ⟦ iden ⟧ (Fin 2)
_ = inj₁ tt , λ x → zero

_ : ⟦ freeₚ 𝟙 ⟧ (Fin 2)
_ = (inj₂ (tt , (λ x → inj₂ (tt , λ x₁ → inj₁ tt)))) , (λ x → suc zero)


maybeₚ : Poly
maybeₚ = 𝟙 + 𝕐

nothing : 𝟙 ⇒ maybeₚ
nothing = leftₚ

justₚ : 𝕐 ⇒ maybeₚ
justₚ = rightₚ

Maybe : Set → Set
Maybe = ⟦ maybeₚ ⟧

--Maybe→AMaybe : ∀{A : Set} → Maybe A → Agda.Maybe A
--Maybe→AMaybe (zero , fib) = Agda.nothing
--Maybe→AMaybe (suc zero , fib) = Agda.just (fib zero)

Just : ∀{A : Set} → A → Maybe A
Just a = ηₚ justₚ (tt , (λ _ → a))

Nothing : ∀{A : Set} → Maybe A
Nothing = ηₚ nothing (tt , (λ ()))

case-maybe : ∀{A B : Set} → B → (A → B) → Maybe A → B
case-maybe cnothing cjust (inj₁ x , args) = cnothing
case-maybe cnothing cjust (inj₂ y , args) = cjust (args tt)

andᶠ : Fin 2 → Fin 2 → Fin 2
andᶠ zero y = zero
andᶠ (suc zero) zero = zero
andᶠ (suc zero) (suc zero) = suc zero

first-monoid : ProposedMonoid (_×ₚ_) 𝟙
P first-monoid = maybeₚ
ε first-monoid = nothing
map-base (_⋆_ first-monoid) (inj₁ tt , inj₁ tt) = inj₁ tt
map-base (_⋆_ first-monoid) (inj₁ tt , inj₂ tt) = inj₂ tt
map-base (_⋆_ first-monoid) (inj₂ tt , inj₁ tt) = inj₂ tt
map-base (_⋆_ first-monoid) (inj₂ tt , inj₂ tt) = inj₂ tt
map-fiber (_⋆_ first-monoid) (inj₁ tt , inj₂ tt) tt = inj₂ tt
map-fiber (_⋆_ first-monoid) (inj₂ tt , inj₁ tt) tt = inj₁ tt
map-fiber (_⋆_ first-monoid) (inj₂ tt , inj₂ tt) tt = inj₁ tt

last-monoid : ProposedMonoid (_×ₚ_) 𝟙
P last-monoid = maybeₚ
ε last-monoid = nothing
map-base (_⋆_ last-monoid) (inj₁ tt , inj₁ tt) = inj₁ tt
map-base (_⋆_ last-monoid) (inj₁ tt , inj₂ tt) = inj₂ tt
map-base (_⋆_ last-monoid) (inj₂ tt , inj₁ tt) = inj₂ tt
map-base (_⋆_ last-monoid) (inj₂ tt , inj₂ tt) = inj₂ tt
map-fiber (_⋆_ last-monoid) (inj₁ tt , inj₂ tt) tt = inj₂ tt
map-fiber (_⋆_ last-monoid) (inj₂ tt , inj₁ tt) tt = inj₁ tt
map-fiber (_⋆_ last-monoid) (inj₂ tt , inj₂ tt) tt = inj₂ tt

-- lemma : (f : maybeₚ .Fiber (inj₂ tt) → maybeₚ .Base) → Σ-syntax (maybeₚ .Fiber (inj₂ tt)) (λ pfib → maybeₚ .Fiber (f pfib))
-- lemma f = tt , {!!}

-- ◁-monoid : ProposedMonoid (_◁_) 𝕐
-- P ◁-monoid = maybeₚ
-- map-base (ε ◁-monoid) tt = inj₁ tt
-- map-fiber (ε ◁-monoid) tt ()
-- map-base (_⋆_ ◁-monoid) (inj₁ tt , f) = inj₁ tt
-- map-base (_⋆_ ◁-monoid) (inj₂ tt , f) with f tt
-- ... | inj₁ _ = inj₁ tt
-- ... | inj₂ _ = inj₂ tt
-- map-fiber (_⋆_ ◁-monoid) (inj₂ tt , f) x = {!!}
-- map-fiber (_⋆_ ◁-monoid) (inj₂ tt , f) x with f tt 
-- ... | inj₂ tt  = tt , {!!}



