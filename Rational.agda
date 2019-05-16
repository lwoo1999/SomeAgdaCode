{-# OPTIONS --safe --cubical #-}
module Rational where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Data.Nat
open import Data.Nat.Solver

import Relation.Binary.PropositionalEquality as P

open +-*-Solver

topath : ∀ {ℓ} {A : Type ℓ} {a b : A} → a P.≡ b → a ≡ b
topath P.refl = refl

data ℚ : Type₀ where
  _/_ : (a b : ℕ) → ℚ
  reduce : (a b a' b' : ℕ) → a * b' ≡ a' * b → a / b ≡ a' / b'
  trunc : isSet ℚ

lemma1 : ∀ a b c d c' d' → c * d' ≡ c' * d → (a * c) / (b * d) ≡ (a * c') / (b * d')
lemma1 a b c d c' d' p = reduce (a * c) (b * d) (a * c') (b * d') eq
  where
  eq : a * c * (b * d') ≡ a * c' * (b * d)
  eq = a * c * (b * d') ≡⟨ topath (solve 4
                                  (λ a c b d' → a :* c :* (b :* d') := a :* b :* (c :* d'))
                                  P.refl a c b d') ⟩
       a * b * (c * d') ≡⟨ cong (a * b *_) p ⟩
       a * b * (c' * d) ≡⟨ topath (solve 4
                                  (λ a b c' d → a :* b :* (c' :* d) := a :* c' :* (b :* d))
                                  P.refl a b c' d) ⟩
       a * c' * (b * d) ∎

lemma2 : ∀ a b c d c' d' → c * d' ≡ c' * d → (c * a) / (d * b) ≡ (c' * a) / (d' * b)
lemma2 a b c d c' d' p = reduce (c * a) (d * b) (c' * a) (d' * b) eq
  where
  eq : c * a * (d' * b) ≡ c' * a * (d * b)
  eq = c * a * (d' * b) ≡⟨ topath (solve 4
                                  (λ c a d' b → c :* a :* (d' :* b) := c :* d' :* (a :* b))
                                  P.refl c a d' b) ⟩
       c * d' * (a * b) ≡⟨ cong (_* (a * b)) p ⟩
       c' * d * (a * b) ≡⟨ topath (solve 4
                                  (λ c' d a b → c' :* d :* (a :* b) := c' :* a :* (d :* b))
                                  P.refl c' d a b) ⟩
       c' * a * (d * b) ∎
  
_ℚ*_ : ℚ → ℚ → ℚ
(a / b) ℚ* (c / d) = (a * c) / (b * d)
(a / b) ℚ* reduce c d c' d' p i = lemma1 a b c d c' d' p i
reduce a b c d x i ℚ* (a₁ / b₁) = lemma2 a₁ b₁ a b c d x i
reduce a b c d x i ℚ* reduce a₁ b₁ a' b' x₁ i₁ =
  isSet→isSet' trunc
  (lemma1 a b a₁ b₁ a' b' x₁)
  (lemma1 c d a₁ b₁ a' b' x₁)
  (lemma2 a₁ b₁ a b c d x)
  (lemma2 a' b' a b c d x) i i₁
trunc m m₁ x y i i₁ ℚ* n =
  trunc (m ℚ* n) (m₁ ℚ* n) (cong (_ℚ* n) x) (cong (_ℚ* n) y) i i₁
m@(_ / _) ℚ* trunc n n₁ x y i i₁ =
  trunc (m ℚ* n) (m ℚ* n₁) (cong (m ℚ*_) x) (cong (m ℚ*_) y) i i₁
m@(reduce _ _ _ _ _ _) ℚ* trunc n n₁ x y i i₁ =
  trunc (m ℚ* n) (m ℚ* n₁) (cong (m ℚ*_) x) (cong (m ℚ*_) y) i i₁

lemma3 : ∀ a b c d c' d' → c * d' ≡ c' * d →
         (a * d + c * b) / (b * d) ≡ (a * d' + c' * b) / (b * d')
lemma3 a b c d c' d' p =
  reduce (a * d + c * b) (b * d) (a * d' + c' * b) (b * d') eq
  where
  eq : (a * d + c * b) * (b * d') ≡ (a * d' + c' * b) * (b * d)
  eq = (a * d + c * b) * (b * d')        ≡⟨ topath (solve 5
                                                   (λ a b c d d' →
                                                   (a :* d :+ c :* b) :* (b :* d') :=
                                                   a :* d :* (b :* d') :+ c :* d' :* b :* b)
                                                   P.refl a b c d d') ⟩
       a * d * (b * d') + c * d' * b * b ≡[ i ]⟨ a * d * (b * d') + p i * b * b ⟩
       a * d * (b * d') + c' * d * b * b ≡⟨ topath (solve 5
                                                   (λ a b c' d d' →
                                                   a :* d :* (b :* d') :+ c' :* d :* b :* b :=
                                                   (a :* d' :+ c' :* b) :* (b :* d))
                                                   P.refl a b c' d d') ⟩
       (a * d' + c' * b) * (b * d)       ∎

lemma4 : ∀ a b c d c' d' → c * d' ≡ c' * d →
         (c * b + a * d) / (d * b) ≡ (c' * b + a * d') / (d' * b)
lemma4 a b c d c' d' p =
  reduce (c * b + a * d) (d * b) (c' * b + a * d') (d' * b) eq
  where
  eq : (c * b + a * d) * (d' * b) ≡ (c' * b + a * d') * (d * b)
  eq = (c * b + a * d) * (d' * b)        ≡⟨ topath (solve 5
                                            (λ a b c d d' →
                                            (c :* b :+ a :* d) :* (d' :* b) :=
                                            c :* d' :* b :* b :+ a :* d :* (d' :* b))
                                            P.refl a b c d d') ⟩
       c * d' * b * b + a * d * (d' * b) ≡[ i ]⟨ p i * b * b + a * d * (d' * b) ⟩
       c' * d * b * b + a * d * (d' * b) ≡⟨ topath (solve 5
                                            (λ a b c' d d' →
                                            c' :* d :* b :* b :+ a :* d :* (d' :* b) :=
                                            (c' :* b :+ a :* d') :* (d :* b))
                                            P.refl a b c' d d') ⟩
       (c' * b + a * d') * (d * b)       ∎

_ℚ+_ : ℚ → ℚ → ℚ
(a / b) ℚ+ (a₁ / b₁) = (a * b₁ + a₁ * b) / (b * b₁)
(a / b) ℚ+ reduce a₁ b₁ a' b' x i = lemma3 a b a₁ b₁ a' b' x i
reduce a b a' b' x i ℚ+ (a₁ / b₁) = lemma4 a₁ b₁ a b a' b' x i
reduce a b a' b' x i ℚ+ reduce a₁ b₁ a'' b'' x₁ i₁ =
  isSet→isSet' trunc
  (lemma3 a b a₁ b₁ a'' b'' x₁)
  (lemma3 a' b' a₁ b₁ a'' b'' x₁)
  (lemma4 a₁ b₁ a b a' b' x)
  (lemma4 a'' b'' a b a' b' x) i i₁
m@(_ / _) ℚ+ trunc n n₁ x y i i₁ =
  trunc (m ℚ+ n) (m ℚ+ n₁) (cong (m ℚ+_) x) (cong (m ℚ+_) y) i i₁
m@(reduce _ _ _ _ _ _) ℚ+ trunc n n₁ x y i i₁ =
  trunc (m ℚ+ n) (m ℚ+ n₁) (cong (m ℚ+_) x) (cong (m ℚ+_) y) i i₁
trunc m m₁ x y i i₁ ℚ+ n =
  trunc (m ℚ+ n) (m₁ ℚ+ n) (cong (_ℚ+ n) x) (cong (_ℚ+ n) y) i i₁
