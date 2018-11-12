module VecRightId where

open import Data.Nat
open import Data.Nat.Properties
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality
open import Data.Vec

lemma : ∀ {m n} {A : Set} (x : A) (xs : Vec A m) (ys : Vec A n) →
        m ≅ n → xs ≅ ys → (x ∷ xs) ≅ (x ∷ ys)
lemma x xs .xs refl refl = refl

xs++[]=xs : ∀ {n} {A : Set} (xs : Vec A n) → xs ++ [] ≅ xs
xs++[]=xs [] = refl
xs++[]=xs {.(suc n)} (_∷_ {n} x xs)
  = lemma x (xs ++ []) xs (≡-to-≅ (+-identityʳ n)) (xs++[]=xs xs)
