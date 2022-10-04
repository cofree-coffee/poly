{-# OPTIONS --type-in-type #-}
module Book.Misc where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Data.Nat
open import Data.Vec

open import Category
open import Functor
open import Isomorphism
open import Representable

------------------------------------------------------------------------------------------
-- Vec Functors

{-
--from-vec : {A : Set} → {n : ℕ} → {F : Set → Set} → {S : Set}
--  → {functor : Functor F} → (F A ≃ Vec A n) → (S ≃ Fin n) → Representable functor
--from-vec {S = S} iso1 iso2 =
--  let finN = (to iso2) {!!}
--  in record { rep = {!!} ; iso = {!!} }

Void≃Fin0 : Void ≃ Fin 0
Void≃Fin0 =
  record { to = λ void →  absurd void
         ; from = λ{ () }
         ; from∘to = λ void →  absurd void
         ; to∘from = λ{ () }
         }

Unit≃Fin1 : Unit ≃ Fin 1
Unit≃Fin1 = 
  record { to = λ{ unit → zero }
         ; from = λ{ zero → unit }
         ; from∘to = λ{ unit → refl }
         ; to∘from = λ{ zero → refl }
         }

MaybeUnit≃Fin2 : Maybe Unit ≃ Fin 2
MaybeUnit≃Fin2 = 
  record { to = λ{ (just unit) → suc zero ; nothing → zero }
         ; from = λ{ zero → nothing ; (suc zero) → just unit }
         ; from∘to = λ{ (just unit) → refl ; nothing → refl }
         ; to∘from = λ{ zero → refl ; (suc zero) → refl }
         }

VecOne≃Identity : {A : Set} → Vec A 1 ≃ Identity A
VecOne≃Identity =
  record { to = λ{ (a ∷ []) → a }
         ; from = λ{ a → a ∷ [] }
         ; from∘to = λ{ (x ∷ []) → refl }
         ; to∘from = λ a → refl
         }

VecTwo≃Pair : {A : Set} → Vec A 2 ≃ Pair A
VecTwo≃Pair =
  record { to = λ{ (x ∷ y ∷ []) → x , y}
         ; from = λ{ (fst , snd) → fst ∷ (snd ∷ []) }
         ; from∘to = λ{ (x ∷ y ∷ []) → refl}
         ; to∘from = λ{ (fst , snd) → refl }
         }

IdentityRepresentableFin : Representable IdentityFunctor
IdentityRepresentableFin =
  record { rep = Fin 1
         ; iso = record { to = λ{ x zero → x }
                        ; from = λ f → f  zero
                        ; from∘to = λ x → refl
                        ; to∘from = λ f → ∀-extensionality λ{ zero → refl }
                        }
         }

Identity≃VecOne : {A : Set} → Identity A ≃ Vec A 1
Identity≃VecOne =
  record { to = λ{ x → x ∷ [] }
         ; from = λ{ (x ∷ []) → x }
         ; from∘to = λ x → refl
         ; to∘from = λ{ (x ∷ []) → refl }
         }

------------------------------------------------------------------------------------------
-- Hom-F

variable
  F G : Set → Set

record _~>_ (f : Functor F) (g : Functor G) : Set where
  field
    η : ∀ {x} → F x → G x

𝕐 : (a : Set) -> (Set -> Set)
𝕐 a x = a → x

Hom-F : (a : Set) → Functor (𝕐 a)
Hom-F a = 
  record
   { fmap = λ f g a → f (g a) 
   ; identity = refl 
   ; composition = refl 
   }

proof : {A B : Set} → (B → A) → Hom-F A ~> Hom-F B
proof f = {!!}
-}
