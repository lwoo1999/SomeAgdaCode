{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Bool

-- transport version apd
apd' : ∀ {i j} {A : Type i} {B : A → Type j} (f : (a : A) → B a)
       {x y : A} → (p : x == y) → transport B p (f x) == f y
apd' f idp = idp

-- hott book 2.9.4
l294 : ∀ {i j} {X : Type i} {x1 x2 : X} (p : x1 == x2)
       {A B : X → Type j} (f : A x1 → B x1) →
       transport (λ x → A x → B x) p f ==
       λ x → transport B p (f (transport A (! p) x))
l294 idp f = λ= λ x → idp

e : Bool ≃ Bool
e = (b->b , λ where
  .g → b->b
  .f-g true → idp
  .f-g false → idp
  .g-f true → idp
  .g-f false → idp
  .adj true → idp
  .adj false → idp)
  where
    b->b : Bool → Bool
    b->b true = false
    b->b false = true

    open is-equiv

p : Bool == Bool
p = ua e

dnl = (A : Type0) → ¬ (¬ A) → A


-- hott book Theorem 3.2.2
t322 : ¬ dnl
t322 f = ff (f Bool λ z → z true) (tt _)
  where
    B = λ A → ¬ (¬ A) → A
    C : ∀ {i} → Type i → Type i
    C = λ A → A
    D = λ A → ¬ (¬ A)

    ⊥id : {a b : ⊥} → a == b
    ⊥id {()}

    -- u : ¬ (¬ Bool) is unique
    uid : {u : ¬ (¬ Bool)} → u == transport D (! p) u
    uid = λ= λ _ → ⊥id

    temp : (u : ¬ (¬ Bool)) →
           transport C p (f Bool u) == f Bool u
    temp u = transport C p (f Bool u) =⟨ ap (λ x → transport C p (f Bool x)) uid ⟩
             transport C p (f Bool (transport D (! p) u)) =⟨ ! (app= (l294 p _) u) ⟩
             transport B p (f Bool) u =⟨ app= (apd' f p) u ⟩
             f Bool u =∎

    ff : ∀ x → coe p x == x → ⊥
    ff true  eq with coe p true  | coe-β e true
    ff true  ()    | _           | idp
    ff false eq with coe p false | coe-β e false
    ff false ()    | _           | idp

    lemma : ∀ {i} {x y : Type i} (p : x == y) → p == ap C p
    lemma idp = idp

    tt : ∀ u → coe p (f Bool u) == f Bool u
    tt u = coe p (f Bool u) =⟨ ap (λ x → coe x (f Bool u)) (lemma _) ⟩
           coe (ap C p) (f Bool u) =⟨ idp ⟩
           transport C p (f Bool u) =⟨ temp u ⟩
           f Bool u =∎
