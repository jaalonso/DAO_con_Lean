-- Demostración de P ∨ Q, ¬(P ∧ Q) ⊢ ¬P ↔ Q
-- ========================================

import tactic
variables  (P Q : Prop)

-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    P ∨ Q, ¬(P ∧ Q) ⊢ ¬P ↔ Q
-- ----------------------------------------------------

-- 1ª demostración
example
  (h₁ : P ∨ Q)
  (h₂ : ¬(P ∧ Q))
  : ¬P ↔ Q :=
begin
  split,
  { intro hnP,
    cases h₁ with hP hQ,
    { exfalso,
      exact hnP hP, },
    { exact hQ }, },
  { intros hQ hP,
    exact h₂ ⟨hP, hQ⟩ },
end

-- 2ª demostración
example
  (h₁ : P ∨ Q)
  (h₂ : ¬(P ∧ Q))
  : ¬P ↔ Q :=
iff.intro
  (assume hnP: ¬P,
   show Q, from
     or.elim h₁
       (assume hP: P,
        show Q,
           from absurd hP hnP)
       (assume hQ,
        show Q,
          from hQ))
  (assume hQ : Q,
   assume hP : P,
   have hPQ : P ∧ Q,
     from and.intro hP hQ,
   show false,
     from h₂ hPQ)

-- 3ª demostración
example
  (h₁ : P ∨ Q)
  (h₂ : ¬(P ∧ Q))
  : ¬P ↔ Q :=
iff.intro
  (assume hnP: ¬P,
   show Q, from
     or.elim h₁
       (assume hP: P,
        show Q,
           from absurd hP hnP)
       (assume hQ,
        show Q,
          from hQ))
  (assume hQ : Q,
   assume hP : P,
   have hPQ : P ∧ Q,
     from and.intro hP hQ,
   h₂ hPQ)

-- 4ª demostración
example
  (h₁ : P ∨ Q)
  (h₂ : ¬(P ∧ Q))
  : ¬P ↔ Q :=
iff.intro
  (assume hnP: ¬P,
   show Q, from
     or.elim h₁
       (assume hP: P,
        show Q,
           from absurd hP hnP)
       (assume hQ,
        show Q,
          from hQ))
  (assume hQ : Q,
   assume hP : P,
   h₂ (and.intro hP hQ))

-- 5ª demostración
example
  (h₁ : P ∨ Q)
  (h₂ : ¬(P ∧ Q))
  : ¬P ↔ Q :=
iff.intro
  (assume hnP: ¬P,
   show Q, from
     or.elim h₁
       (assume hP: P,
        show Q,
           from absurd hP hnP)
       (assume hQ,
        show Q,
          from hQ))
  (λ hQ hP, h₂ (and.intro hP hQ))

-- 6ª demostración
example
  (h₁ : P ∨ Q)
  (h₂ : ¬(P ∧ Q))
  : ¬P ↔ Q :=
iff.intro
  (assume hnP: ¬P,
   show Q, from
     or.elim h₁
       (assume hP: P,
        show Q,
           from absurd hP hnP)
       (assume hQ,
        hQ))
  (λ hQ hP, h₂ (and.intro hP hQ))

-- 7ª demostración
example
  (h₁ : P ∨ Q)
  (h₂ : ¬(P ∧ Q))
  : ¬P ↔ Q :=
iff.intro
  (assume hnP: ¬P,
   show Q, from
     or.elim h₁
       (assume hP: P,
        show Q,
           from absurd hP hnP)
       (λ hQ, hQ))
  (λ hQ hP, h₂ (and.intro hP hQ))

-- 8ª demostración
example
  (h₁ : P ∨ Q)
  (h₂ : ¬(P ∧ Q))
  : ¬P ↔ Q :=
iff.intro
  (assume hnP: ¬P,
   show Q, from
     or.elim h₁
       (assume hP: P,
        show Q,
           from absurd hP hnP)
       id)
  (λ hQ hP, h₂ (and.intro hP hQ))

-- 9ª demostración
example
  (h₁ : P ∨ Q)
  (h₂ : ¬(P ∧ Q))
  : ¬P ↔ Q :=
iff.intro
  (assume hnP: ¬P,
   show Q, from
     or.elim h₁
       (assume hP: P,
        absurd hP hnP)
       id)
  (λ hQ hP, h₂ (and.intro hP hQ))

-- 10ª demostración
example
  (h₁ : P ∨ Q)
  (h₂ : ¬(P ∧ Q))
  : ¬P ↔ Q :=
iff.intro
  (assume hnP: ¬P,
   show Q, from
     or.elim h₁
       (λ hP, absurd hP hnP)
       id)
  (λ hQ hP, h₂ (and.intro hP hQ))

-- 11ª demostración
example
  (h₁ : P ∨ Q)
  (h₂ : ¬(P ∧ Q))
  : ¬P ↔ Q :=
iff.intro
  (assume hnP: ¬P,
   or.elim h₁ (λ hP, absurd hP hnP) id)
  (λ hQ hP, h₂ (and.intro hP hQ))

-- 12ª demostración
example
  (h₁ : P ∨ Q)
  (h₂ : ¬(P ∧ Q))
  : ¬P ↔ Q :=
iff.intro
  (λ hnP, or.elim h₁ (λ hP, absurd hP hnP) id)
  (λ hQ hP, h₂ (and.intro hP hQ))

-- 13ª demostración
example
  (h₁ : P ∨ Q)
  (h₂ : ¬(P ∧ Q))
  : ¬P ↔ Q :=
-- by hint
by finish
