open import Data.Maybe
open import Function
open import Level
open import Relation.Binary.PropositionalEquality

postulate
  extensionality : ∀ {α β} {S : Set α} {T : S → Set β}
                   {f g : (x : S) → T x} →
                   ((x : S) → f x ≡ g x) →
                   f ≡ g

record _↔_ {α β} (P : Set α) (Q : Set β) : Set (α ⊔ β) where
  field
    p→q : P → Q
    q→p : Q → P
    pqp : q→p ∘ p→q ≡ id
    qpq : p→q ∘ q→p ≡ id

↔trans : ∀ {α β} {P : Set α} {Q : Set β} → P ↔ Q → Q ↔ P
↔trans record
       { p→q = p→q
       ; q→p = q→p
       ; pqp = pqp
       ; qpq = qpq
       }
       =
       record
       { p→q = q→p
       ; q→p = p→q
       ; pqp = qpq
       ; qpq = pqp
       }

lemma : ∀ {α β} {P : Set α} {Q : Set β} (p↔q : P ↔ Q) →
        ∀ p₁ p₂ → _↔_.p→q p↔q p₁ ≡ _↔_.p→q p↔q p₂ → p₁ ≡ p₂
lemma record
      { p→q = p→q
      ; q→p = q→p
      ; pqp = pqp
      ; qpq = qpq
      }
      p₁ p₂ q≡ = begin
        p₁
          ≡⟨ cong (_|>_ p₁) (sym pqp) ⟩
        q→p (p→q p₁)
          ≡⟨ cong q→p q≡ ⟩
        q→p (p→q p₂)
          ≡⟨ cong (_|>_ p₂) pqp ⟩
        p₂
          ∎
      where
        open ≡-Reasoning

isoUnMaybe : ∀ {α β} (P : Set α) (Q : Set β) → Maybe P ↔ Maybe Q → P ↔ Q
isoUnMaybe
  P Q
  mp↔mq @ record
  { p→q = mp→mq
  ; q→p = mq→mp
  ; pqp = mpqp
  ; qpq = mqpq
  }
  =
  record
  { p→q = p→q
  ; q→p = q→p
  ; pqp = extensionality pqp
  ; qpq = extensionality qpq
  }
  where
    p→q : P → Q
    p→q p with mp→mq (just p) | inspect mp→mq (just p) | mp→mq nothing | inspect mp→mq nothing
    ...      | just q         | _                      | _             | _                     = q
    ...      | nothing        | _                      | just q        | _                     = q
    ...      | nothing        | [ ≡nothing₁ ]          | nothing       | [ ≡nothing₂ ]         with lemma mp↔mq (just p) nothing
                                                                                                    (trans ≡nothing₁ (sym ≡nothing₂))
    ...                                                                                           | ()

    q→p : Q → P
    q→p q with mq→mp (just q) | inspect mq→mp (just q) | mq→mp nothing | inspect mq→mp nothing
    ...      | just p         | _                      | _             | _                     = p
    ...      | nothing        | _                      | just p        | _                     = p
    ...      | nothing        | [ ≡nothing₁ ]          | nothing       | [ ≡nothing₂ ]         with lemma (↔trans mp↔mq) (just q) nothing
                                                                                                    (trans ≡nothing₁ (sym ≡nothing₂))
    ...                                                                                           | ()

    open ≡-Reasoning

    lempq₁ : ∀ p q → mp→mq (just p) ≡ just q → p→q p ≡ q
    lempq₁ p q meq with mp→mq (just p) | inspect mp→mq (just p)
    ...               | just q1        | _ = just-injective meq
    lempq₁ p q ()     | nothing        | _

    lempq₂ : ∀ p q → mp→mq (just p) ≡ nothing → mp→mq nothing ≡ (just q) → p→q p ≡ q
    lempq₂ p q j≡n n≡j with mp→mq (just p) | inspect mp→mq (just p) | mp→mq nothing | inspect mp→mq nothing
    ...                   | nothing        | _                      | just q1       | _ = just-injective n≡j
    lempq₂ p q j≡n ()     | nothing        | _                      | nothing       | _
    lempq₂ p q () n≡j     | just q1        | _                      | _             | _

    qpq : ∀ q → (p→q (q→p q)) ≡ q
    qpq q with mq→mp (just q) | inspect mq→mp (just q)
    ...      | just p         | [ ≡just ] = lempq₁ p q (begin
      mp→mq (just p)
        ≡⟨ sym (cong mp→mq ≡just) ⟩
      mp→mq (mq→mp (just q))
        ≡⟨ cong (_|>_ (just q)) mqpq ⟩
      just q
        ∎
      )
    ...      | nothing        | [ ≡nothing₁ ] with mq→mp nothing | inspect mq→mp nothing
    ...                                          | just p        | [ ≡just ] = lempq₂ p q
        (begin
      mp→mq (just p)
        ≡⟨ sym (cong mp→mq ≡just) ⟩
      mp→mq (mq→mp nothing)
        ≡⟨ cong (_|>_ nothing) mqpq ⟩
      nothing
        ∎)
        (begin
      mp→mq nothing
        ≡⟨ sym (cong mp→mq ≡nothing₁) ⟩
      mp→mq (mq→mp (just q))
        ≡⟨ cong (_|>_ (just q)) mqpq ⟩
      just q
        ∎)
    ...                                          | nothing       | [ ≡nothing₂ ] with lemma (↔trans mp↔mq) (just q) nothing
                                                                                      (trans ≡nothing₁ (sym ≡nothing₂))
    ...                                                                             | ()

    pqp : ∀ p → (q→p (p→q p)) ≡ p
    pqp p = {!!}
