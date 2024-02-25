module Poly.Types.Maybe where

--------------------------------------------------------------------------------

open import Data.Fin using (Fin; suc; zero)
open import Data.Product using (_,_)
import Data.Maybe as Agda
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Poly
open import Poly.Monoid
open import Poly.Monoidal.Coproduct
open import Poly.Monoidal.Product

--------------------------------------------------------------------------------

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
