open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.List
open import Data.List.Properties

lemma : ∀ a b → a ≡ suc b + a → ⊥
lemma (suc a) b p =
  lemma a b (suc-injective (trans p (cong suc (+-suc b a))))

++-injectiveˡ : ∀ {ℓ} {A : Set ℓ} (a b c : List A) → a ++ c ≡ b ++ c → a ≡ b
++-injectiveˡ [] [] c p = refl
++-injectiveˡ [] (x ∷ b) c p =
  ⊥-elim (lemma _ _ (trans (cong length p) (length-++ (x ∷ b))))
++-injectiveˡ (x ∷ a) [] c p =
  ⊥-elim (lemma _ _ (trans (sym (cong length p)) (length-++ (x ∷ a))))
++-injectiveˡ (x ∷ a) (y ∷ b) c p
  with ∷-injectiveˡ p | ++-injectiveˡ a b c (∷-injectiveʳ p)
...  | refl           | refl
  = refl

++-injectiveʳ : ∀ {ℓ} {A : Set ℓ} (a b c : List A) → a ++ b ≡ a ++ c → b ≡ c
++-injectiveʳ [] b c p = p
++-injectiveʳ (x ∷ a) b c p
  rewrite ++-injectiveʳ a b c (∷-injectiveʳ p) =
  refl
