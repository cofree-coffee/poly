{-# OPTIONS --type-in-type #-}
module Chapter2 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

open import Function using (_∘_)
open import Data.Empty
open import Data.Nat
open import Data.Fin
open import Data.Vec using (Vec; _∷_; []; map; lookup; tabulate)

-- The following modules live here: https://github.com/solomon-b/category-theory
open import Category
open import Category.Sets
open import Category.Op
open import Functor
open import FunExt
open import Isomorphism
open import NaturalTransformation
open import Representable
open import Data.Reader
open import Category.Endofunctors

------------------------------------------------------------------------------------------

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
    ; id = λ x → refl
    ; composition = λ x → refl
    ; cong-mapₘ = λ{ prf (fst , snd) → cong₂ _,_ (prf fst) (prf snd) }
    }

-- | 'Pair A' is isomorphic to 'Bool → A'
Pair≃Bool→A : { A : Set } → Sets [ Pair A ≅ Sets [ Bool , A ] ]
Pair≃Bool→A =
  record
    { to = λ{ (fst , snd) false → fst ; (fst , snd) true → snd }
    ; from = λ f → ( f false , f true )
    ; from⨟to = λ f → ∀-extensionality λ{ false → refl ; true → refl }
    ; to⨟from = λ x → refl
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
    ; id = λ _ → refl
    ; composition = λ _ → refl
    ; cong-mapₘ = λ{ prf x → prf x }
    }

-- | 'Identity A' is isomorphic to 'Unit → A'
Identity≃Unit→a : {A : Set} → Sets [ Identity A ≅ Sets [ Unit , A ] ]
Identity≃Unit→a =
  record
    { to = λ a unit → a
    ; from = λ f → f unit
    ; from⨟to = λ f → ∀-extensionality (λ{ unit → refl })
    ; to⨟from = λ _ → refl
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
    ; id = λ _ → refl
    ; composition = λ _ → refl
    ; cong-mapₘ = λ _ _ → refl
    }

ConstBoolFunctor : EndoFunctor Sets
ConstBoolFunctor = ConstFunctor Bool

unit-unique : ∀ (x y : Unit) → x ≡ y
unit-unique unit unit = refl

!-unique : ∀ {A : Set} → (f g : A → Unit) → f ≡ g
!-unique f g = ∀-extensionality λ x → unit-unique (f x) (g x)

true≢false : true ≡ false → ⊥
true≢false ()

pointwise : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ x → f x ≡ g x
pointwise refl x = refl

const-bool-not-representable : Representable Sets ConstBoolFunctor → ⊥
const-bool-not-representable record { rep = rep ; iso = iso } =
  let iso' = iso { a = Unit }
  in
  true≢false
   (
    begin
      true
    ≡⟨ refl ⟩
      Const true unit
    ≡⟨ sym ((to⨟from iso') true) ⟩
      from iso' (to iso' true)
    ≡⟨ cong (from iso') (!-unique (to iso' true) (to iso' false)) ⟩
      from iso' (to iso' false)
    ≡⟨ (to⨟from iso') false ⟩
      Const false unit
    ≡⟨ refl ⟩
      false
    ∎
   )

-- 3) 'Const Unit' is 'Representable' by '⊥'

ConstUnitFunctor : EndoFunctor Sets
ConstUnitFunctor = ConstFunctor Unit

ConstUnit≃Void→a : {A : Set} → Sets [ Unit ≅ Sets [ ⊥ , A ] ]
ConstUnit≃Void→a =
  record
    { to = λ{ unit void → ⊥-elim void }
    ; from = λ _ → unit
    ; from⨟to = λ f → ∀-extensionality (λ void → ⊥-elim void)
    ; to⨟from = λ{ unit → refl }
    }

ConstUnitRepresentable : Representable Sets ConstUnitFunctor
ConstUnitRepresentable =
  record { rep = ⊥
         ; iso = ConstUnit≃Void→a
         }

-- 4) 'Const Void' is not 'Representable'

Const-⊥-Functor : EndoFunctor Sets
Const-⊥-Functor = ConstFunctor ⊥

const-⊥-not-representable : Representable Sets Const-⊥-Functor → ⊥
const-⊥-not-representable
  record { rep = rep ; iso = iso } =
    let iso' = iso {a = Unit}
    in from iso' (λ _ → unit)

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
mapₒ (VecNFunctor n) = λ a → Vec a n
mapₘ (VecNFunctor n) = λ{ f xs → map f xs }
id (VecNFunctor n) = (vec-unit n)
composition (VecNFunctor n) = λ{ [] → refl ; (x ∷ xs) → map-comp x xs }
cong-mapₘ (VecNFunctor .zero) prf [] = refl
cong-mapₘ (VecNFunctor (suc n)) prf (x ∷ xs) = cong₂ _∷_ (prf x) (cong-mapₘ (VecNFunctor n) prf xs)


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
    ; from⨟to = λ f → ∀-extensionality (from⨟to-lemma f)
    ; to⨟from = to⨟from-lemma
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

------------------------------------------------------------------------------------------
-- Proposition 2.5

{-
For any function 'f : R → S', there is a 'NaturalTransformation' 'y^f : y^S → y^R'.

On any set 'X', the X-Component 'X^f : X^S → X^R' is given by sending 'g : S → X' 'f ⨟ g : R → X'.

In other words:

Given:

f : R → S

We get a natural transformation:

y^f : (S → y) → (R → y)

Which can be applied to any set @y@:

X^f : (S → X) → (R → X)
X^f g = f ⨟ g

-}

------------------------------------------------------------------------------------------
-- Exercise 2.6

{-
Prove that for any function '𝑓 : 𝑅 → 𝑆', what we said was a natural
transformation in Proposition 2.5 really is natural. That is, for any
function 'ℎ : 𝑋 → 𝑌', show that the following diagram commutes:
-}

proof : {R S : Set} → (R → S) → NaturalTransformation (ReaderFunctor S) (ReaderFunctor R)
proof f =
  record
    { η = λ _ g r → g (f r)
    ; commute = λ h g → refl
    }

------------------------------------------------------------------------------------------
-- Exercise 2.7

{-
Let '𝑋' be an arbitrary set. For each of the following sets '𝑅', '𝑆' and
functions '𝑓 : 𝑅 → 𝑆', describe the 𝑋-component of, i.e. the function 𝑋^𝑆
→ 𝑋^𝑅 coming from, the natural transformation y^𝑓 : y^𝑆 → y^𝑅.

1. 𝑅 = 5, 𝑆 = 5, 𝑓 = id. (Here you’re supposed to give a function called 𝑋^id5 : 𝑋^5 →
𝑋^5.)
2. 𝑅 = 2, 𝑆 = 1, 𝑓 is the unique function.
3. 𝑅 = 1, 𝑆 = 2, 𝑓 (1) = 1
-}

-- 1)
exercise-27-1 : {X : Set} → (Fin 5 → X) → Fin 5 → X
exercise-27-1 f fin = f fin

-- 2)
exercise-27-2 : {X : Set} → (Fin 1 → X) → Fin 2 → X
exercise-27-2 f fin = f zero

-- 3)
weaken : {n : ℕ} → Fin n → Fin (suc n)
weaken zero = zero
weaken (suc fin) = suc (weaken fin)

exercise-27-3 : {X : Set} → (Fin 2 → X) → Fin 1 → X
exercise-27-3 f fin = f (weaken fin)

------------------------------------------------------------------------------------------
-- Exercise 2.8

{-
Show that the construction in Proposition 2.5 is functorial:

  y⁻ : Set^op → [Set, Set]

as follows.

1. Show that for any set '𝑆', we have that 'y^id𝑆 : y^𝑆 → y^𝑆' is the identity.
2. Show that for any functions '𝑓 : 𝑅 → 𝑆' and '𝑔 : 𝑆 → 𝑇', we have y^𝑔 ⨟ y^𝑓 = y^(𝑓⨟𝑔) .
-}

-- A mapping from the objects of Set^op to the objects of [Set, Set]
y⁻ₒ : (ob (Op Sets)) → Functor Sets Sets
y⁻ₒ R =
  record
    { mapₒ = λ A → (R → A)
    ; mapₘ = λ f g r → f (g r)
    ; id = (λ f → refl)
    ; composition = (λ f → refl)
    ; cong-mapₘ = λ prf f → ∀-extensionality (λ x → prf (f x))
    }

-- A mapping of morphisms that involves 'y⁻ₒ'
y⁻ₘ : {x y : ob (Op Sets)} → Op Sets [ x , y ] → EndoFunctorCategory [ y⁻ₒ x , y⁻ₒ y ]
y⁻ₘ h =
  record
    { η = λ X f y → f (h y)
    ; commute = λ f _ → refl
    }

y⁻ : Functor (Op Sets) (EndoFunctorCategory)
mapₒ y⁻ = y⁻ₒ
mapₘ y⁻ = y⁻ₘ
id y⁻ = λ _ _ → refl
composition y⁻ = λ _ _ → refl
cong-mapₘ y⁻ = λ prf X f → ∀-extensionality (λ x → cong f (prf x))
