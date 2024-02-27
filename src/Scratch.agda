module Scratch where

open import Data.Vec
open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Fin hiding (_+_)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Poly
open import Poly.Monoidal.Product
open import Poly.Monoidal.Tensor
open import Poly.Monoidal.Coproduct renaming (_+_ to _+ₚ_)
open import Poly.SetFunctor using (_≃_)

nyan : Poly
Base nyan =  ℕ
Fiber nyan = λ _ → ℕ

hotel : nyan ⇒ 𝕐^ ℕ +ₚ 𝕐
map-base hotel = λ where
  -- where one is our floor 57 cause pattern matching on nats is annoying
  zero → inj₁ tt
  (suc zero) → inj₂ tt
  (suc (suc x)) → inj₁ tt
map-fiber hotel zero delta = delta
map-fiber hotel (suc zero) tt = zero
map-fiber hotel (suc (suc curr)) delta = (suc (suc curr)) + delta

AyA : (A : Set) → Poly
Base (AyA A) = A
Fiber (AyA A) = λ _ → A

cool-map : (A : Set) → AyA A ⊗ AyA A ⊗ AyA A ⇒ AyA A
map-base (cool-map A) = λ where
  (a1 , a2 , a3) → a3
map-fiber (cool-map A) (a1 , a2 , a3) ain = ain , (a1 , a2)


cool-map2 : (A : Set) → AyA A ⊗ AyA A ⊗ AyA A ⇒ AyA A
map-base (cool-map2 A) = λ where
  (a1 , a2 , a3) → a3
map-fiber (cool-map2 A) (a1 , a2 , a3) ain = a2 , (a1 , ain)

ℕy : Poly
Base ℕy = ℕ
Fiber ℕy = λ _ → ⊤

funny : ℕy ⊗ ℕy ⊗ 𝕐^ ℕ ⇒ 𝕐 
map-base funny x = tt
map-fiber funny (n1 , n2 , tt) tt = tt , (tt , n1 + n2)


nat-to-vec : (n : ℕ) → Vec Bool n
nat-to-vec zero = []
nat-to-vec (suc n) = true ∷ nat-to-vec n

elim : (motive : ℕ → Set) → motive 0 → ((n : ℕ) → motive n → motive (suc n)) → (n : ℕ) → motive n
elim motive z f zero = z
elim motive z f (suc n) = f n (elim motive z f n)

nat-to-vec' : (n : ℕ) → Vec ⊤ n
nat-to-vec' n = elim (λ n → Vec ⊤  n) [] (λ n xs → tt ∷ xs) n

bool-elim : (motive : Bool → Set) → motive true → motive false → (p : Bool) → motive p
bool-elim motive t f false = f
bool-elim motive t f true = t

data BoolList : Set where
  Nil : BoolList
  Cons : Bool → BoolList → BoolList

boolList-elim : ∀{A : Set} → A → (Bool → A → A) → BoolList → A
boolList-elim nil cons Nil = nil
boolList-elim nil cons (Cons x xs) = cons x (boolList-elim nil cons xs)

all : BoolList → Bool
all xs = boolList-elim true (λ p q → p ∧ q) xs

tabulate' : ∀{A : Set} → (Fin 2 → A) → (A × A)
tabulate' f = (f zero) , (f (suc zero))

index' : ∀{A : Set} → (A × A) → Fin 2 → A
index' (a , b) zero = a
index' (a , b) (suc z) = b


uhh : Σ[ ty ∈ Set ] (ty → Set)
uhh = ⊤ , λ x → Bool


{-
   Γ ⊢ p : P        Γ ⊢ q : Q
--------------------------
   Γ ⊢ (p , q) : P × Q
-}
⟨_,_⟩ₚ : ∀{Γ P Q : Poly} → Γ ⇒ P → Γ ⇒ Q → Γ ⇒ (P ×ₚ Q)
⟨ f , g ⟩ₚ .map-base γ = f .map-base γ , g .map-base γ
⟨ f , g ⟩ₚ .map-fiber γ (inj₁ p) = map-fiber f γ p
⟨ f , g ⟩ₚ .map-fiber γ (inj₂ q) = map-fiber g γ q

cool : ∀{Γ P Q : Poly} → Γ ⇒ P → Γ ⇒ Q → Γ ⇒ (P ×ₚ (Q ×ₚ P))
cool p q = ⟨ p , ⟨ q , p ⟩ₚ ⟩ₚ
