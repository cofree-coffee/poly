{-# OPTIONS --type-in-type #-}
module Chapter2 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
open ≡-Reasoning

open import Function using (_∘_)
open import Data.Empty
open import Data.Nat
open import Data.Fin
open import Data.Vec using (Vec; _∷_; []; map; lookup; tabulate)

open import Category
open import Functor
open import Isomorphism
open import Representable

------------------------------------------------------------------------------------------

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

data Bool : Set where
  false true : Bool

------------------------------------------------------------------------------------------
-- Pair

-- | 'Pair A' is the functor that sends every set 𝕏 to 𝕏×𝕏,
record Pair (A : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : A

PairFunctor : EndoFunctor Sets
PairFunctor =
  record
    { mapₒ = Pair
    ; mapₘ = λ{ f (fst , snd) → ( f fst , f snd ) }
    ; id = refl
    ; composition = refl
    }

-- | 'Pair A' is isomorphic to 'Bool → A'
Pair≃Bool→A : { A : Set } → Sets [ Pair A ≅ Sets [ Bool , A ] ]
Pair≃Bool→A =
  record
    { to = λ{ (fst , snd) false → fst ; (fst , snd) true → snd }
    ; from = λ f → ( f false , f true )
    ; from⨟to = ∀-extensionality λ f → ∀-extensionality λ{ false → refl ; true → refl }
    ; to⨟from = refl
    }

-- | Making it 'Representable' by 'Bool'
PairRepresentable : Representable Sets PairFunctor
PairRepresentable =
  record
    { rep = Bool
    ; iso = Pair≃Bool→A
    }

------------------------------------------------------------------------------------------
-- Exercise 2.4

{-
Exercise 2.4
For each of the following functors Set → Set, say if it is
representable or not; if it is, say what the representing set is.
1. (Identity A) The identity functor 𝑋 ↦→ 𝑋, which sends each function to itself.
2. (Const Bool) The constant functor 𝑋 ↦→ 2, which sends every function to the identity on 2.
3. (Const Unit) The constant functor 𝑋 ↦→ 1, which sends every function to the identity on 1.
4. (Const Void) The constant functor 𝑋 ↦→ 0, which sends every function to the identity on 0.
5. A functor 𝑋 ↦→ 𝑋^ℕ. If it were representable, where would it send each function?
6. A functor 𝑋 ↦→ 2^𝑋. If it were representable, where would it send each function?
-}

-- 1) 'Identity' is 'Representable' by 'Unit'.

-- | 'Identity A' is the functor that maps 'A' to itself. 
Identity : {A : Set} → A → A
Identity A = A

data Unit : Set where
  unit : Unit

IdentityFunctor : EndoFunctor Sets 
IdentityFunctor =
  record
    { mapₒ = Identity
    ; mapₘ = λ f x → Identity (f x)
    ; id = refl
    ; composition = refl
    }

-- | 'Identity A' is isomorphic to 'Unit → A'
Identity≃Unit→a : {A : Set} → Sets [ Identity A ≅ Sets [ Unit , A ] ]
Identity≃Unit→a =
  record
    { to = λ a unit → a
    ; from = λ f → f unit
    ; from⨟to = ∀-extensionality (λ f → ∀-extensionality (λ{ unit → refl }))
    ; to⨟from = refl
    }

-- | Making it Representable by 'unit'
IdentityRepresentable : Representable Sets IdentityFunctor
IdentityRepresentable =
  record { rep = Unit
         ; iso = Identity≃Unit→a
         }

-- 2) 'Const Bool' is not 'Representable'
-- We can demonstrate this by picking out some 'A' where the two sides of the Iso have different cardinalities:
--
-- Constant Bool Unit ≅ ? → Unit
-- const True           const unit
-- const False

Const : {A B : Set} → A → B → A
Const A = λ _ → A

ConstFunctor : (A : Set) → EndoFunctor Sets
ConstFunctor A =
  record
    { mapₒ = Const A
    ; mapₘ = λ f x → x
    ; id = refl
    ; composition = refl
    }

ConstBoolFunctor : EndoFunctor Sets
ConstBoolFunctor = ConstFunctor Bool

unit-unique : ∀ (x y : Unit) → x ≡ y
unit-unique unit unit = refl

!-unique : ∀ {A : Set} → (f g : A → Unit) → f ≡ g
!-unique f g = ∀-extensionality λ x → unit-unique (f x) (g x)

true≢false : true ≡ false → ⊥
true≢false ()

-- Const Bool Unit ≅ _ → Unit

-- to : Const Bool Unit → (_ → Unit)
-- from : (_ → Unit)  → Const Bool Unit

-- from⨟to : from ⨟ to ≡ _ → Unit
-- to⨟from : to ⨟ from ≡ Const Bool Unit

const-bool-not-representable : Representable Sets ConstBoolFunctor → ⊥
const-bool-not-representable record { rep = rep ; iso = iso } =
  let iso' = iso { a = Unit }
  in
  true≢false
   (
    begin
      true
    ≡⟨ {!!} ⟩
      false
    ∎
   )

--ConstBool-!Representable : {A : Set} → ({∀ x : Set} → Constant Bool A ≃ (x → A)) → ⊥
--ConstBool-!Representable iso = {!!}

-- 3) 'Const Unit' is 'Representable' by '⊥'

ConstUnitFunctor : EndoFunctor Sets
ConstUnitFunctor = ConstFunctor Unit

ConstUnit≃Void→a : {A : Set} → Sets [ Unit ≅ Sets [ ⊥ , A ] ]
ConstUnit≃Void→a =
  record
    { to = λ{ unit void → ⊥-elim void }
    ; from = λ _ → unit
    ; from⨟to = ∀-extensionality λ f → ∀-extensionality (λ void → ⊥-elim void)
    ; to⨟from = ∀-extensionality (λ{ unit → refl })
    }

ConstUnitRepresentable : Representable Sets ConstUnitFunctor
ConstUnitRepresentable =
  record { rep = ⊥
         ; iso = ConstUnit≃Void→a
         }

-- 4) 'Const Void' is not 'Representable'

ConstFunctorVoid : EndoFunctor Sets
ConstFunctorVoid = ConstFunctor ⊥

--ConstVoid-!Representable : {A : Set} → ({∀ x : Set} → Constant Void A ≃ (x → A)) → Void
--ConstVoid-!Representable iso = {!!}

-- 5) 'X ↦→ 𝑋^ℕ' is 'Representable' trivially by itself ('ℕ → X'):  'ℕ → A ≅ ℕ → A'

-- We can also demonstrate that for any value of ℕ, we get a 'Representable':

vec-unit : {A : Set} → (n : ℕ)  → (vec : Vec A n)  → map (λ x → x) vec ≡ vec
vec-unit zero [] = refl
vec-unit (suc n) (x ∷ vec) = cong (λ vec → x ∷ vec) (vec-unit n vec)

map-comp : {A B C : Set} → {f : A → B} → {g : B → C} → {n : ℕ}
  → (x : A) → (xs : Vec A n) → (g ∘ f) x ∷ map (g ∘ f) xs ≡ (map g ∘ map f) (x ∷ xs)
map-comp {f = f} {g = g} {n = zero} x [] = refl
map-comp {f = f} {g = g} {n = suc n} x (y ∷ xs) = cong (λ ys → g (f x) ∷ ys) (map-comp y xs)

VecNFunctor : ℕ → EndoFunctor Sets
VecNFunctor n =
  record
    { mapₒ = λ a → Vec a n
    ; mapₘ = λ{ f xs → map f xs }
    ; id = ∀-extensionality (vec-unit n)
    ; composition = ∀-extensionality λ{ [] → refl ; (x ∷ xs) → map-comp x xs }
    } 

from⨟to-lemma : {A : Set} → {n : ℕ} → (f : Sets [ Fin n , A ]) → (x : Fin n) → (Sets [ tabulate ⨟ lookup ]) f x ≡ f x
from⨟to-lemma f zero = refl
from⨟to-lemma f (suc x) = from⨟to-lemma (f ∘ suc) x

to⨟from-lemma : {A : Set} → {n : ℕ} → (x : Vec A n) → (Sets [ lookup ⨟ tabulate ]) x ≡ x
to⨟from-lemma [] = refl
to⨟from-lemma (x ∷ xs) = cong (λ ys → x ∷ ys) (to⨟from-lemma xs)

VecN≅FinN : {A : Set} → (n : ℕ) → Sets [ Vec A n ≅ Sets [ Fin n , A ] ]
VecN≅FinN n =
  record
    { to = lookup
    ; from = tabulate
    ; from⨟to = ∀-extensionality (λ f → ∀-extensionality (from⨟to-lemma f))
    ; to⨟from = ∀-extensionality to⨟from-lemma
    }

VecNFinRepresentable : (n : ℕ) → Representable Sets (VecNFunctor n)
VecNFinRepresentable n =
  record { rep = Fin n
         ; iso = VecN≅FinN n
         }

-- 6) '𝑋 ↦→ 2^𝑋' is not 'Representable' (under this definition): 'A → Bool'
--    is 'Contravariant' and thus we cannot define 'A → Bool ≅ ? → A'
--
-- We can further demonstrate this by picking out a particular 'A'
-- where the cardinalities of the two sides of the iso must be
-- different regardless of the 'rep':
--
-- Unit → Bool ≅ ? → A
-- 
-- const true    const ()
-- const false
