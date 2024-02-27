{-# OPTIONS --type-in-type #-}
module Poly.Types.Tuple where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Fin using (Fin; zero; suc)
open import Poly
open import Poly.Monoidal
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------


2-tuple : Poly
2-tuple .Base = Fin 1
2-tuple .Fiber = λ _ → Fin 2

2-Tuple : Set → Set → Set
2-Tuple A B = ⟦ 2-tuple ⟧ (A × B)

-- mk-tuple : ∀{A : Set} → A → A → 2-Tuple A
-- mk-tuple a b = zero , (λ where
--   zero → a
--   (suc x) → b)

-- fst : ∀{A : Set} → 2-Tuple A → A
-- fst (_ , fiber) = fiber zero

-- snd : ∀{A : Set} → 2-Tuple A → A
-- snd (_ , fiber) = fiber (suc zero)

-- _ : ∀ {m n : ℕ} → fst (mk-tuple m n) ≡ m
-- _ = refl

-- _ : ∀ {m n : ℕ} → snd (mk-tuple m n) ≡ n
-- _ = refl
