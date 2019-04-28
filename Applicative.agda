{-# OPTIONS --cubical --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (_∘_)

id : ∀ {ℓ} {A : Set ℓ} → A → A
id x = x

_∘_ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
      (f : B → C) (g : A → B) → A → C
f ∘ g = λ x → f (g x)

record Applicative (F : Set → Set) : Set1 where
  infixl 5 _<*>_
  
  field

    pure : {A : Set} → A → F A
    _<*>_ : {A B : Set} → F (A → B) → F A → F B

    identity : {A : Set} (v : F A) → pure id <*> v ≡ v
    
    composition : {A B C : Set} (u : F (B → C)) (v : F (A → B)) (w : F A) →
                  pure _∘_ <*> u <*> v <*> w ≡ u <*> (v <*> w)

    homomorphism : {A B : Set} (f : A → B) (x : A) →
                   pure f <*> pure x ≡ pure (f x)

    interchange : {A B : Set} (u : F (A → B)) (y : A) →
                  u <*> pure y ≡ pure (λ f → f y) <*> u

compose : ∀ {F G} → Applicative F → Applicative G → Applicative (F ∘ G)
compose {F} {G} AF AG = res
  where
    open Applicative ⦃ ... ⦄
    
    instance
      ApplicativeF : Applicative F
      ApplicativeF = AF

      ApplicativeG : Applicative G
      ApplicativeG = AG

    res : Applicative (F ∘ G)
    Applicative.pure res = pure ∘ pure
    Applicative._<*>_ res fs xs = pure _<*>_ <*> fs <*> xs
    Applicative.identity res v =
      pure _<*>_ <*> pure (pure id) <*> v
        ≡⟨ cong (λ x → _<*>_ {F = F} x v) (homomorphism _<*>_ (pure id)) ⟩
      pure (pure id <*>_) <*> v
        ≡⟨ cong (λ x → pure x <*> v) (funExt identity) ⟩
      pure id <*> v
        ≡⟨ identity v ⟩
      v
        ∎

    Applicative.composition res u v w =
      (pure _<*>_ <*>
       ((pure _<*>_ <*> (pure _<*>_ <*> pure (pure _∘_) <*> u))
        <*> v)) <*> w
        ≡[ i ]⟨ (pure _<*>_ <*>
                ((pure _<*>_ <*> (homomorphism _<*>_ (pure _∘_) i <*> u))
                <*> v)) <*> w ⟩
      (pure _<*>_ <*>
       ((pure _<*>_ <*> (pure (pure _∘_ <*>_) <*> u))
        <*> v)) <*> w
        ≡[ i ]⟨ (pure _<*>_ <*>
                (composition (pure _<*>_) (pure (pure _∘_ <*>_)) u (~ i)
                <*> v)) <*> w ⟩
      (pure _<*>_ <*>
       ((pure _∘_ <*> pure _<*>_ <*> pure (pure _∘_ <*>_) <*> u)
        <*> v)) <*> w
        ≡[ i ]⟨ (pure _<*>_ <*>
                ((homomorphism _∘_ _<*>_ i <*> pure (pure _∘_ <*>_) <*> u)
                <*> v)) <*> w ⟩
      (pure _<*>_ <*>
       ((pure (_∘_ _<*>_) <*> pure (pure _∘_ <*>_) <*> u)
        <*> v)) <*> w
        ≡[ i ]⟨ (pure _<*>_ <*>
                ((homomorphism (_∘_ _<*>_) (pure _∘_ <*>_) i <*> u)
                <*> v)) <*> w ⟩
      pure _<*>_ <*> ((pure (λ x → (pure _∘_ <*> x) <*>_) <*> u) <*> v) <*> w
        ≡[ i ]⟨ composition (pure _<*>_)
                (pure (λ x → (pure _∘_ <*> x) <*>_) <*> u) v (~ i) <*> w ⟩
      pure _∘_ <*> pure _<*>_ <*> (pure (λ x → (pure _∘_ <*> x) <*>_) <*> u)
      <*> v <*> w
        ≡[ i ]⟨ homomorphism _∘_ _<*>_ i
                <*> (pure (λ x → (pure _∘_ <*> x) <*>_) <*> u) <*> v <*> w ⟩
      pure (_∘_ _<*>_) <*> (pure (λ x → (pure _∘_ <*> x) <*>_) <*> u)
      <*> v <*> w
        ≡[ i ]⟨ composition (pure (_∘_ _<*>_))
                (pure (λ x → (pure _∘_ <*> x) <*>_)) u (~ i) <*> v <*> w ⟩
      pure _∘_ <*> pure (_∘_ _<*>_) <*> pure (λ x → (pure _∘_ <*> x) <*>_)
      <*> u <*> v <*> w
        ≡[ i ]⟨ homomorphism _∘_ (_∘_ _<*>_) i <*>
                pure (λ x → (pure _∘_ <*> x) <*>_) <*> u <*> v <*> w ⟩
      pure (_∘_ (_∘_ _<*>_)) <*> pure (λ x → (pure _∘_ <*> x) <*>_) <*> u
      <*> v <*> w
        ≡[ i ]⟨ homomorphism (_∘_ (_∘_ _<*>_)) (λ x → (pure _∘_ <*> x) <*>_) i
                <*> u <*> v <*> w ⟩
      pure (_∘_ _<*>_ ∘ (λ x → (pure _∘_ <*> x) <*>_)) <*> u <*> v <*> w
        ≡⟨ refl ⟩
      pure (λ x y z → pure _∘_ <*> x <*> y <*> z) <*> u <*> v <*> w
        ≡[ i ]⟨ pure (λ x y z → composition x y z i) <*> u <*> v <*> w ⟩
      pure (λ x y z → x <*> (y <*> z)) <*> u <*> v <*> w
        ≡⟨ refl ⟩
      pure ((_∘_ (λ f → f _<*>_)) ((_∘_ _∘_) (_∘_ _∘_ _<*>_))) <*> u <*> v <*> w
        ≡[ i ]⟨ homomorphism (_∘_ (λ f → f _<*>_)) ((_∘_ _∘_) (_∘_ _∘_ _<*>_))
                (~ i) <*> u <*> v <*> w ⟩
      pure (_∘_ (λ f → f _<*>_)) <*> pure ((_∘_ _∘_) (_∘_ _∘_ _<*>_))
      <*> u <*> v <*> w
        ≡[ i ]⟨ homomorphism _∘_ (λ f → f _<*>_) (~ i)
        <*> pure ((_∘_ _∘_) (_∘_ _∘_ _<*>_)) <*> u <*> v <*> w ⟩
      pure (_∘_) <*> pure (λ f → f _<*>_) <*> pure ((_∘_ _∘_) (_∘_ _∘_ _<*>_)) 
      <*> u <*> v <*> w
        ≡[ i ]⟨ composition (pure (λ f → f _<*>_))
               (pure ((_∘_ _∘_) (_∘_ _∘_ _<*>_))) u i <*> v <*> w ⟩
      pure (λ f → f _<*>_) <*> (pure ((_∘_ _∘_) (_∘_ _∘_ _<*>_)) <*> u)
      <*> v <*> w
        ≡[ i ]⟨ interchange (pure ((_∘_ _∘_) (_∘_ _∘_ _<*>_)) <*> u) _<*>_ (~ i)
                <*> v <*> w ⟩
      pure ((_∘_ _∘_) (_∘_ _∘_ _<*>_)) <*> u <*> pure _<*>_ <*> v <*> w
        ≡[ i ]⟨ homomorphism (_∘_ _∘_) (_∘_ _∘_ _<*>_) (~ i)
                <*> u <*> pure _<*>_ <*> v <*> w ⟩
      pure (_∘_ _∘_) <*> pure (_∘_ _∘_ _<*>_) <*> u <*> pure _<*>_ <*> v <*> w
        ≡[ i ]⟨ homomorphism _∘_ _∘_ (~ i) <*> pure (_∘_ _∘_ _<*>_) <*> u <*> pure
                _<*>_ <*> v <*> w ⟩
      pure _∘_ <*> pure _∘_ <*> pure (_∘_ _∘_ _<*>_) <*> u <*> pure _<*>_
      <*> v <*> w
        ≡[ i ]⟨ composition (pure _∘_) (pure (_∘_ _∘_ _<*>_)) u i <*>
                pure _<*>_ <*> v <*> w ⟩
      pure _∘_ <*> (pure (_∘_ _∘_ _<*>_) <*> u) <*> pure _<*>_ <*> v <*> w
        ≡[ i ]⟨ composition (pure (_∘_ _∘_ _<*>_) <*> u) (pure _<*>_) v i <*> w ⟩
      pure (_∘_ _∘_ _<*>_) <*> u <*> (pure _<*>_ <*> v) <*> w
        ≡[ i ]⟨ homomorphism (_∘_ _∘_) _<*>_ (~ i)
                <*> u <*> (pure _<*>_ <*> v) <*> w ⟩
      pure (_∘_ _∘_) <*> pure _<*>_ <*> u <*> (pure _<*>_ <*> v) <*> w
        ≡[ i ]⟨ homomorphism _∘_ _∘_ (~ i)
                <*> pure _<*>_ <*> u <*> (pure _<*>_ <*> v) <*> w ⟩
      pure _∘_ <*> pure _∘_ <*> pure _<*>_ <*> u <*> (pure _<*>_ <*> v) <*> w
        ≡[ i ]⟨ composition (pure _∘_) (pure _<*>_) u i
                <*> (pure _<*>_ <*> v) <*> w ⟩
      pure _∘_ <*> (pure _<*>_ <*> u) <*> (pure _<*>_ <*> v) <*> w
        ≡⟨ composition (pure _<*>_ <*> u) (pure _<*>_ <*> v) w ⟩
      pure _<*>_ <*> u <*> (pure _<*>_ <*> v <*> w) 
        ∎

    Applicative.homomorphism res f x =
      pure _<*>_ <*> pure (pure f) <*> pure (pure x)
        ≡[ i ]⟨ homomorphism _<*>_ (pure f) i <*> pure (pure x) ⟩
      pure (pure f <*>_) <*> pure (pure {F = G} x)
        ≡⟨ homomorphism (pure f <*>_) (pure x)  ⟩
      pure (pure f <*> pure x)
        ≡⟨ cong pure (homomorphism f x) ⟩
      pure (pure (f x))
        ∎

    Applicative.interchange res u y =
      pure _<*>_ <*> u <*> pure (pure y)
        ≡⟨ interchange (pure _<*>_ <*> u) (pure y)  ⟩
      pure (λ v → v (pure y)) <*> (pure _<*>_ <*> u)
        ≡⟨ sym (composition (pure (λ v → v (pure y))) (pure _<*>_) u) ⟩
      pure _∘_ <*> pure (λ v → v (pure y)) <*> pure _<*>_ <*> u
        ≡[ i ]⟨ homomorphism _∘_ (λ v → v (pure y)) i <*> pure _<*>_ <*> u  ⟩
      pure ((λ v → v (pure y)) ∘_) <*> pure _<*>_ <*> u
        ≡[ i ]⟨ homomorphism ((λ v → v (pure y)) ∘_) _<*>_ i <*> u  ⟩
      pure (λ v → v <*> pure y) <*> u
        ≡[ i ]⟨ pure (λ v → interchange v y i) <*> u ⟩
      pure (λ v → pure (λ f → f y) <*> v) <*> u
        ≡[ i ]⟨ homomorphism _<*>_ (pure (λ f → f y)) (~ i) <*> u ⟩
      pure _<*>_ <*> pure (pure (λ f → f y)) <*> u
        ∎
