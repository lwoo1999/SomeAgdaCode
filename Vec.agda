module Vec where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool renaming (Bool to 𝔹)
open import Data.Vec renaming (Vec to 𝕍)
open import Function
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
  hiding (zip)
open import Relation.Binary.PropositionalEquality
  hiding ([_])

transpose : ∀ {ℓ m n} {A : Set ℓ} → 𝕍 (𝕍 A n) m → 𝕍 (𝕍 A m) n
transpose {n = zero} [] = []
transpose {n = suc n} [] = [] ∷ (transpose [])
transpose (xs ∷ xss) = zipWith (flip _∷_) (transpose xss) xs

_ : transpose (
    (1 ∷ 2 ∷ 3 ∷ []) ∷
    (4 ∷ 5 ∷ 6 ∷ []) ∷
    (7 ∷ 8 ∷ 9 ∷ []) ∷ []
    ) ≡
    (1 ∷ 4 ∷ 7 ∷ []) ∷
    (2 ∷ 5 ∷ 8 ∷ []) ∷
    (3 ∷ 6 ∷ 9 ∷ []) ∷ []
_ = refl

filter : ∀ {ℓ m} {A : Set ℓ} (p : A → 𝔹) → 𝕍 A m → ∃[ n ] 𝕍 A n
filter p [] = zero , []
filter p (x ∷ xs) with p x   | filter p xs
...                  | true  | n , ind = (suc n) , x ∷ ind
...                  | false | n , ind = n , ind

filter-id : ∀ {ℓ m} {A : Set ℓ} (p : A → 𝔹) (xs : 𝕍 A m) →
            fst (filter p xs) + fst (filter (not ∘ p) xs) ≡ m
filter-id p [] = refl
filter-id p (x ∷ xs) with p x
...                      | true rewrite filter-id p xs = refl
...                      | false
  rewrite +-suc (fst (filter p xs)) (fst (filter (not ∘ p) xs))
        | filter-id p xs = refl

lesseq : ℕ → ℕ → 𝔹
lesseq 0 y = true
lesseq (suc x) zero = false
lesseq (suc x) (suc y) = lesseq x y

qsort₁ : ∀ m n → m ≤ n → 𝕍 ℕ m → 𝕍 ℕ m
qsort₁ 0 n z≤n [] = []
qsort₁ (suc m) (suc n) (s≤s m≤n) (x ∷ xs)
  rewrite sym (filter-id (lesseq x) xs)
        = subst (𝕍 ℕ)
          (solve 2 (λ l r → l :+ (con 1 :+ r) := con 1 :+ l :+ r) refl l r)
          (qsort₁ l n l≤n left ++ [ x ] ++ qsort₁ r n r≤n right)
  where
    lf : ∃[ n ] 𝕍 ℕ n
    lf = filter (lesseq x) xs
  
    l : ℕ
    l = fst lf

    left : 𝕍 ℕ l
    left = snd lf

    rf : ∃[ n ] 𝕍 ℕ n
    rf = filter (not ∘ lesseq x) xs

    r : ℕ
    r = fst rf

    right : 𝕍 ℕ r
    right = snd rf

    l≤n : l ≤ n
    l≤n = begin
      l
        ≤⟨ m≤m+n l r  ⟩
      l + r
        ≤⟨ m≤n ⟩
      n
        ∎
      where
        open ≤-Reasoning

        
    r≤n : r ≤ n
    r≤n = begin
      r
        ≤⟨ m≤m+n r l ⟩
      r + l
        ≤⟨ ≤-reflexive (+-comm r l) ⟩
      l + r
        ≤⟨ m≤n ⟩
      n
        ∎
      where
        open ≤-Reasoning

    open import Data.Nat.Solver
    open +-*-Solver

qsort : ∀ {m} → 𝕍 ℕ m → 𝕍 ℕ m
qsort {m} = qsort₁ m m ≤-refl

_ : qsort (1 ∷ 3 ∷ 8 ∷ 4 ∷ 9 ∷ [])
          ≡
          9 ∷ 8 ∷ 4 ∷ 3 ∷ 1 ∷ []
_ = refl

_ : qsort (7 ∷ 8 ∷ 4 ∷ 4 ∷ 1 ∷ [])
    ≡
    8 ∷ 7 ∷ 4 ∷ 4 ∷ 1 ∷ []
_ = refl  
