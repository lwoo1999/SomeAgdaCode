open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.List
open import Data.List.Properties
open import Function

lemma : ∀ a b → a ≡ suc b + a → ⊥
lemma (suc a) b p =
  lemma a b a=sucb+a
  where
    open ≡-Reasoning

    a=sucb+a : a ≡ suc b + a
    a=sucb+a = suc-injective $ begin
      suc a           ≡⟨ p ⟩
      suc (b + suc a) ≡⟨ cong suc (+-suc b a) ⟩
      suc (suc b) + a ∎

++-injectiveˡ : ∀ {ℓ} {A : Set ℓ} (a b c : List A) → a ++ c ≡ b ++ c → a ≡ b
++-injectiveˡ [] [] c p = refl
++-injectiveˡ [] (x ∷ b) c p =
  ⊥-elim $ lemma _ _ eq
  where
    open ≡-Reasoning
    
    eq : length c ≡ suc (length b) + length c
    eq = begin
      length c                  ≡⟨ cong length p ⟩
      length (x ∷ b ++ c)       ≡⟨ length-++ (x ∷ b) ⟩
      suc (length b) + length c ∎
++-injectiveˡ (x ∷ a) [] c p =
  ⊥-elim $ lemma _ _ eq

  where
    open ≡-Reasoning

    eq : length c ≡ suc (length a) + length c
    eq = begin
      length c                  ≡⟨ sym (cong length p) ⟩
      length (x ∷ a ++ c)       ≡⟨ length-++ (x ∷ a) ⟩
      suc (length a) + length c ∎
++-injectiveˡ (x ∷ a) (y ∷ b) c p
  with ∷-injectiveˡ p | ++-injectiveˡ a b c $ ∷-injectiveʳ p
...  | refl           | refl
  = refl

++-injectiveʳ : ∀ {ℓ} {A : Set ℓ} (a b c : List A) → a ++ b ≡ a ++ c → b ≡ c
++-injectiveʳ [] b c p = p
++-injectiveʳ (x ∷ a) b c p
  rewrite ++-injectiveʳ a b c $ ∷-injectiveʳ p =
  refl
