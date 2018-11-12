module Sort where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Nat.Properties
open import Data.Vec
open import Data.Vec.All as A
open import Relation.Nullary
open import Data.Empty

data _IsSortedBy_ {ℓ} {A : Set ℓ} :
     ∀ {n} → Vec A n → (A → A → Set) → Set ℓ where
  sortedempty : ∀ {_>_} → [] IsSortedBy _>_
  sortedsucc : ∀ {_>_ n} {xs : Vec A n} {x : A} (p : All (_>_ x) xs) →
               xs IsSortedBy _>_ → (x ∷ xs) IsSortedBy _>_
             
insertNat : ∀ {n} → Nat → Vec Nat n → Vec Nat (suc n)
insertNat x [] = x ∷ []
insertNat x (y ∷ xs) with x ≤? y
... | yes _ = x ∷ y ∷ xs
... | no _ = y ∷ insertNat x xs

insertSort : ∀ {n} → Vec Nat n → Vec Nat n
insertSort [] = []
insertSort (x ∷ xs) = insertNat x (insertSort xs)

insertSorted : ∀ {n} x (xs : Vec Nat n) →
               xs IsSortedBy _≤_ → (insertNat x xs) IsSortedBy _≤_
insertSorted x [] sortedempty = sortedsucc [] sortedempty
insertSorted x (y ∷ xs) (sortedsucc p p₁)
  with x ≤? y
...  | yes x≤y = sortedsucc (x≤y ∷ A.map (≤-trans x≤y) p)
                            (sortedsucc p p₁)
...  | no x≰y = sortedsucc (lemma xs p) (insertSorted x xs p₁)
  where
    lemma : ∀ {n} → (xs : Vec Nat n) →
            All (_≤_ y) xs → All (_≤_ y) (insertNat x xs)
    lemma [] p = ≰⇒≥ x≰y ∷ p
    lemma (z ∷ xs) p with x ≤? z
    lemma (z ∷ xs) p | yes x≤z = ≰⇒≥ x≰y ∷ p
    lemma (z ∷ xs) (y<z ∷ p) | no x≰z = y<z ∷ lemma xs p

insertSortSorted : ∀ {n} (xs : Vec Nat n) → insertSort xs IsSortedBy _≤_
insertSortSorted [] = sortedempty
insertSortSorted (x ∷ xs) = insertSorted x (insertSort xs)
                                           (insertSortSorted xs)
 
