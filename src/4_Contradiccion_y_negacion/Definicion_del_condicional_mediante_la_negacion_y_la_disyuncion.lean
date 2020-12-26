-- Definición del condicional mediante la negación y la disyunción
-- ===============================================================

import tactic

variables (P Q : Prop)

open_locale classical

-- ----------------------------------------------------
-- Ejercicio. Demostrar que
--    (P → Q) ↔ (¬ P ∨ Q)
-- ----------------------------------------------------

-- 1ª demostración
example :
  (P → Q) ↔ (¬ P ∨ Q) :=
begin
  split,
  { intro hPQ,
    by_cases hP : P,
    { right,
      apply hPQ,
      exact hP, },
    { left,
      exact hP, }},
  { intros h hP,
    cases h with hnP hQ,
    { exact absurd hP hnP, },
    { exact hQ, }},
end

-- 2ª demostración
example :
  (P → Q) ↔ (¬ P ∨ Q) :=
begin
  split,
  { intro hPQ,
    by_cases hP : P,
    { exact or.inr (hPQ hP), },
    { exact or.inl hP, }},
  { rintros (hnP | hQ) hP,
    { exact absurd hP hnP, },
    { exact hQ, }},
end

-- 3ª demostración
example :
  (P → Q) ↔ (¬ P ∨ Q) :=
iff.intro
  ( assume hPQ : P → Q,
    show ¬P ∨ Q, from
      or.elim (em P)
      ( assume hP : P,
        have hQ : Q,
          from hPQ hP,
        show ¬P ∨ Q,
          from or.inr hQ)
      ( assume hnP : ¬P,
        show ¬P ∨ Q,
          from or.inl hnP))
  ( assume hnPQ : ¬P ∨ Q,
    assume hP: P,
    show Q, from
      or.elim hnPQ
        ( assume hnP : ¬P,
          show Q,
            from absurd hP hnP)
        ( assume hQ : Q,
          show Q,
            from hQ))

-- 4ª demostración
example :
  (P → Q) ↔ (¬ P ∨ Q) :=
iff.intro
  (λ hPQ, or.elim (em P)
    (λ hP,  or.inr (hPQ hP))
    (λ hnP, or.inl hnP))
  (λ hnPQ hP, or.elim hnPQ
    (λ hnP, absurd hP hnP)
    id)

-- 5ª demostración
example :
  (P → Q) ↔ (¬ P ∨ Q) :=
-- by library_search
imp_iff_not_or

-- 6ª demostración
example :
  (P → Q) ↔ (¬ P ∨ Q) :=
⟨λ hPQ, if hP : P then or.inr (hPQ hP) else or.inl hP,
 λ hnPQ hP, or.elim hnPQ (λ hnP, absurd hP hnP) id⟩

-- 7ª demostración
example :
  (P → Q) ↔ (¬ P ∨ Q) :=
-- by hint
by tauto

-- 8ª demostración
example :
  (P → Q) ↔ (¬ P ∨ Q) :=
by finish
