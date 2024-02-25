{-# OPTIONS --type-in-type #-}
module Poly.Types.List where

--------------------------------------------------------------------------------

open import Data.Fin using (Fin; suc; zero; toℕ; inject₁; splitAt)
import Data.List as Agda
open Agda using (_∷_; [])
import Data.Maybe as Agda
open import Data.Empty
open import Data.Nat using (ℕ; _+_; suc; zero; _⊔_)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Sum using (_⊎_; [_,_]; inj₁; inj₂)
open import Data.Unit using (tt)
open import Poly
open import Poly.Monoid
open import Poly.Monoidal.Compose
open import Poly.Monoidal.Coproduct hiding (_+_)
open import Poly.Monoidal.Product
open import Poly.Monoidal.Or
open import Poly.Types.Maybe

--------------------------------------------------------------------------------

listₚ : Poly
listₚ .Base = ℕ
listₚ .Fiber n = Fin n

nil : 𝟙 ⇒ listₚ
map-base nil tt = zero
map-fiber nil _ ()

cons : 𝕐 ×ₚ listₚ ⇒ listₚ
map-base cons (tt , n) = suc n
map-fiber cons (tt , n) zero = inj₁ tt
map-fiber cons (tt , n) (suc x) = inj₂ x

List-recₚ : {R : Poly} → (𝟙 ⇒ R) → (𝕐 ×ₚ R) ⇒ R → listₚ ⇒ R

List-recₚ {R = R} enil econs = foldₚ
  module List-recₚ where
  base-rec : ℕ → R .Base
  base-rec zero = enil .map-base tt
  base-rec (suc n) = econs .map-base (tt , base-rec n)

  fib-rec : ∀ (n : ℕ) → R .Fiber (base-rec n) → Fin n
  fib-rec zero r' = ⊥-elim (enil .map-fiber tt r')
  fib-rec (suc n) r' with econs .map-fiber (tt , base-rec n) r'
  ... | inj₁ tt = zero
  ... | inj₂ r'' = suc (fib-rec n r'')

  foldₚ : listₚ ⇒ R
  foldₚ .map-base = base-rec
  foldₚ .map-fiber = fib-rec

{-# DISPLAY List-recₚ.foldₚ = List-recₚ #-}

List : Set → Set
List = ⟦ listₚ ⟧

List→ADT : ∀{A : Set} → List A → Agda.List A
List→ADT (base , fib) = Agda.tabulate fib

Nil : ∀{A : Set} → List A
Nil = zero , λ ()

Cons : ∀{A : Set} → A → List A → List A
Cons a (tag , args) = (suc tag) , λ where
  zero → a
  (suc x) → args x

ex : Agda.List ℕ
ex = List→ADT (Cons 20 (Cons 1 Nil))

maybeₚ⇒listₚ : maybeₚ ⇒ listₚ
maybeₚ⇒listₚ .map-base (inj₁ tt) = zero
maybeₚ⇒listₚ .map-base (inj₂ tt) = suc zero
maybeₚ⇒listₚ .map-fiber (inj₂ tt) zero = tt

maybe⇒List : ∀{A : Set} → Maybe A → List A
maybe⇒List maybe = maybeₚ⇒listₚ ⟨$⟩ maybe

-- | A list of maybe values
list-maybeₚ : Poly
list-maybeₚ = listₚ ◁ maybeₚ

List-Maybe : Set → Set
List-Maybe = ⟦ list-maybeₚ ⟧

empty : List-Maybe ℕ
empty = (zero , λ ()) , λ ()

-- ex2 : Agda.List (Maybe ℕ)
-- ex2 = List→ADT {!ex2!}

-- just-nil : List-Maybe ℕ
-- just-nil = (suc zero , λ _ → zero ) , λ ()

-- just-cons : {A : Set} → A → List A → List-Maybe A
-- just-cons a (tag , args) = (suc tag , λ where x → suc zero) , λ x → a

×-monoid : ProposedMonoid (_×ₚ_) 𝟙
P ×-monoid = listₚ
map-base (ε ×-monoid) tt = zero
map-fiber (ε ×-monoid) tt ()
map-base (_⋆_ ×-monoid) (n , m) = n + m
map-fiber (_⋆_ ×-monoid) (n , m) x = splitAt n x

Σ-map : ∀ {A A' : Set} {P : A → Set} {Q : A' → Set}
  → (f : A → A')
  → (g : ∀ {a} → P a → Q (f a))
  → Σ[ a ∈ A ] (P a) → Σ[ a' ∈ A' ] (Q a')
Σ-map f g (x , y) = f x , g y

vcons : ∀ {A : Set} {n : ℕ} → A → (Fin n → A) → (Fin (suc n) → A)
vcons x xs zero = x
vcons x xs (suc i) = xs i

list : ∀ {A : Set} → Agda.List A → ⟦ listₚ ⟧ A
list [] = 0 , (λ ())
list (x ∷ xs) = Σ-map suc (vcons x) (list xs)

l1 : ⟦ listₚ ⟧ ℕ
l1 = list (zero ∷ 1 ∷ 2 ∷ [])

l2 : ⟦ listₚ ⟧ ℕ
l2 = list (2 ∷ [])

alignₚ : ∀{ Γ : Poly } → Γ ⇒ listₚ → Γ ⇒ listₚ → Γ ⇒ (listₚ ◁ ({!!} ∨ {!!}))
alignₚ = {!!}

