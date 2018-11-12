module MSort where

open import Data.Product
open import Function
open import Size
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (compare; Ordering)

infixr 5 _∷_
data List {ℓ} (A : Set ℓ) : {ι : Size} → Set ℓ where
  []  : ∀ {ι} →                  List A {↑ ι}
  _∷_ : ∀ {ι} → A → List A {ι} → List A {↑ ι}

split : ∀ {ℓ ι} {A : Set ℓ} → List A {ι} → List A {ι} × List A {ι}
split [] = [] , []
split (x ∷ xs) with split xs
...               | ls , rs = x ∷ rs , ls

data Ordering : Set where
  lt : Ordering
  eq : Ordering
  gt : Ordering

record Ord {ℓ} (A : Set ℓ) : Set ℓ where
  field compare : A → A → Ordering

open Ord

instance OrdNat : Ord ℕ
compare OrdNat zero zero = eq
compare OrdNat zero (suc n) = lt
compare OrdNat (suc m) zero = gt
compare OrdNat (suc m) (suc n) = compare OrdNat m n

merge : ∀ {ℓ ι} {A : Set ℓ} {{OrdA : Ord A}} →
        List A {ι} → List A → List A
merge ⦃ OrdA ⦄ [] ys = ys
merge ⦃ OrdA ⦄ xs [] = xs
merge ⦃ OrdA ⦄ (x ∷ xs) (y ∷ ys)
  with compare OrdA x y
...  | lt = x ∷ merge xs (y ∷ ys)
...  | _  = y ∷ merge (x ∷ xs) ys

merge-sort : ∀ {ℓ ι} {A : Set ℓ} {{OrdA : Ord A}} → List A {ι} → List A
merge-sort [] = []
merge-sort (x ∷ []) = x ∷ []
merge-sort (x ∷ y ∷ xs)
  with split xs
...  | ls , rs = merge (merge-sort $ x ∷ ls) (merge-sort $ y ∷ rs)
