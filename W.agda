{-# OPTIONS --cubical --safe #-}
module W where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Everything
open import Data.List hiding ([_])

record Reveal_·_is_ {a b} {A : Set a} {B : A → Set b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set (ℓ-max a b) where
  constructor [_]
  field eq : f x ≡ y

inspect : ∀ {a b} {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = [ refl ]

data W (A : Type₀) (B : A → Type₀) : Type₀ where
  sup : (a : A) → (B a → W A B) → W A B

Bℕ : Bool → Type₀
Bℕ false = ⊥
Bℕ true = Unit

ℕᵂ : Type₀
ℕᵂ = W Bool Bℕ

ℕ→ℕᵂ : ℕ → ℕᵂ
ℕ→ℕᵂ 0 = sup false ⊥-elim
ℕ→ℕᵂ (suc n) = sup true λ _ → ℕ→ℕᵂ n

ℕᵂ→ℕ : ℕᵂ → ℕ
ℕᵂ→ℕ (sup false _) = 0
ℕᵂ→ℕ (sup true x) = suc (ℕᵂ→ℕ (x _))

ℕ→ℕᵂ→ℕ : ∀ n → ℕᵂ→ℕ (ℕ→ℕᵂ n) ≡ n
ℕ→ℕᵂ→ℕ zero = refl
ℕ→ℕᵂ→ℕ (suc n) i = suc (ℕ→ℕᵂ→ℕ n i)

ℕᵂ→ℕ→ℕᵂ : ∀ n → ℕ→ℕᵂ (ℕᵂ→ℕ n) ≡ n
ℕᵂ→ℕ→ℕᵂ (sup false x) = cong (sup false) (funExt λ b → ⊥-elim b)
ℕᵂ→ℕ→ℕᵂ (sup true x) = cong (sup true) (funExt (λ _ → ℕᵂ→ℕ→ℕᵂ (x _)))

ℕ≡ℕᵂ : ℕ ≡ ℕᵂ
ℕ≡ℕᵂ = ua (isoToEquiv (iso ℕ→ℕᵂ ℕᵂ→ℕ ℕᵂ→ℕ→ℕᵂ ℕ→ℕᵂ→ℕ))

Listᵂ : Type₀ → Type₀
Listᵂ A = W (Unit ⊎ A) λ {(inl _) → ⊥ ; (inr _) → Unit}

List→Listᵂ : ∀ {A} → List A → Listᵂ A
List→Listᵂ [] = sup (inl _) ⊥-elim
List→Listᵂ (x ∷ xs) = sup (inr x) λ _ → List→Listᵂ xs

Listᵂ→List : ∀ {A} → Listᵂ A → List A
Listᵂ→List (sup (inl _) _) = []
Listᵂ→List (sup (inr x) xs) = x ∷ Listᵂ→List (xs _)

List→Listᵂ→List : ∀ {A} (xs : List A) → Listᵂ→List (List→Listᵂ xs) ≡ xs
List→Listᵂ→List [] = refl
List→Listᵂ→List (x ∷ xs) = cong (x ∷_) (List→Listᵂ→List xs)

Listᵂ→List→Listᵂ : ∀ {A} (xs : Listᵂ A) → List→Listᵂ (Listᵂ→List xs) ≡ xs
Listᵂ→List→Listᵂ (sup (inl tt) x) = cong (sup (inl tt)) (funExt (λ b → ⊥-elim b))
Listᵂ→List→Listᵂ (sup (inr x) xs) = cong (sup (inr x)) (funExt (λ _ → Listᵂ→List→Listᵂ (xs _)))

List≡Listᵂ : ∀ {A} → List A ≡ Listᵂ A
List≡Listᵂ = ua (isoToEquiv (iso List→Listᵂ Listᵂ→List Listᵂ→List→Listᵂ List→Listᵂ→List))

WAlg : (A : Type₀) → (A → Type₀) → Type₁
WAlg A B = Σ Type₀ (λ C → (a : A) → (B a → C) → C)

WAlg-ℕᵂ : WAlg Bool Bℕ
WAlg-ℕᵂ = ℕᵂ , sup

WAlg-ℕ : WAlg Bool Bℕ
WAlg-ℕ = ℕ , λ {false _ → 0 ; true b → suc (b _)}

WHom : (A : Type₀) (B : A → Type₀) (C D : WAlg A B) → Type₀
WHom A B (C , Sc) (D , Sd) =
  Σ (C → D) (λ f → (a : A) → (h : B a → C) → f (Sc a h) ≡ Sd a (f ∘ h))

WHom-ℕ-ℕᵂ : WHom Bool Bℕ WAlg-ℕ WAlg-ℕᵂ
WHom-ℕ-ℕᵂ .fst = ℕ→ℕᵂ
WHom-ℕ-ℕᵂ .snd false _ = cong (sup false) (funExt (λ b → ⊥-elim b))
WHom-ℕ-ℕᵂ .snd true h
  with inspect h _
...  | [ p ] = λ i → sup true λ _ → ℕ→ℕᵂ (p (~ i))

isHinit : (A : Type₀) (B : A → Type₀) (I : WAlg A B) → Type₁
isHinit A B I = (C : WAlg A B) → isContr (WHom A B I C)

module _ (A : Type₀) (B : A → Type₀) (E : WAlg A B) where

  D : WAlg A B
  D = W A B , sup

  C = fst E
  Sc = snd E

  f : W A B → C
  f (sup a b) = Sc a (f ∘ b)

  Sf : (a : A) (h : B a → W A B) →
       snd E a (λ x → f (h x)) ≡ snd E a (λ x → f (h x))
  Sf _ _ = refl

  W-isHinit′ : isContr (WHom A B D E)
  W-isHinit′ .fst = f , Sf
  W-isHinit′ .snd (g , Sg) = λ i → f=g i , λ a h → Sf=Sg a h i
    where
    fx=gx : ∀ x → f x ≡ g x
    fx=gx (sup a b) = (λ i → Sc a λ x → fx=gx (b x) i) ∙ sym (Sg a b)

    f=g = funExt fx=gx

    Sf=Sg : (a : A) (h : B a → W A B) →
            PathP (λ i → f=g i (sup a h) ≡ Sc a (f=g i ∘ h))
                  (Sf a h) (Sg a h)
            -- f (sup a h) ≡ Sc a (f ∘ h)
            -- g (sup a h) ≡ Sc a (g ∘ h)
    Sf=Sg a h i j = hcomp
                    (λ k → λ { (i = i0) → Sf a h (~ k ∨ j)
                             ; (i = i1) → Sg a h (~ k ∨ j)
                             ; (j = i1) → (Sc a (f=g i ∘ h))
                             }) 
                    (Sc a (f=g i ∘ h))

W-isHinit : ∀ A B → isHinit A B (W A B , sup)
W-isHinit = W-isHinit′
