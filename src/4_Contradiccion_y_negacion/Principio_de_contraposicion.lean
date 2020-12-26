-- Principio de contraposición
-- ===========================

import tactic

variables  (P Q : Prop)

open_locale classical

-- ----------------------------------------------------
-- Ejercicio. Demostrar el principio de contraposición
--    (P → Q) ↔ (¬Q → ¬P)
-- ----------------------------------------------------

-- 1ª demostración
example :
  (P → Q) ↔ (¬Q → ¬P) :=
begin
  split,
  { intros hPQ hnQ hP,
    apply hnQ,
    apply hPQ,
    exact hP,},
  { intros hQP hP,
    by_contradiction hnQ,
    apply absurd hP,
    apply hQP,
    exact hnQ, },
end

-- 2ª demostración
example :
  (P → Q) ↔ (¬Q → ¬P) :=
begin
  split,
  { intros hPQ hnQ hP,
    exact hnQ (hPQ hP),},
  { intros hQP hP,
    by_contradiction hnQ,
    exact absurd hP (hQP hnQ), },
end

-- 3ª demostración
example :
  (P → Q) ↔ (¬Q → ¬P) :=
begin
  split,
  { exact λ hPQ hnQ hP, hnQ (hPQ hP), },
  { exact λ hQP hP, by_contradiction (λ hnQ , absurd hP (hQP hnQ)), },
end

-- 4ª demostración
example :
  (P → Q) ↔ (¬Q → ¬P) :=
⟨λ hPQ hnQ hP, hnQ (hPQ hP),
 λ hQP hP, by_contradiction (λ hnQ , absurd hP (hQP hnQ))⟩

-- 4ª demostración
example :
  (P → Q) ↔ (¬Q → ¬P) :=
iff.intro
  ( assume hPQ : P → Q,
    assume hnQ : ¬Q,
    assume hP : P,
    have hQ : Q,
      from hPQ hP,
    show false,
      from hnQ hQ )
  ( assume hQP : (¬Q → ¬P),
    assume hP : P,
    show Q, from
      by_contradiction
        ( assume hnQ : ¬Q,
          have hnP : ¬P,
            from hQP hnQ,
          show false,
            from hnP hP))

-- 5ª demostración
example :
  (P → Q) ↔ (¬Q → ¬P) :=
iff.intro
  (λ hPQ hnQ hP, hnQ (hPQ hP))
  (λ hQP hP, by_contradiction (λ hnQ, (hQP hnQ) hP))

-- 6ª demostración
example :
  (P → Q) ↔ (¬Q → ¬P) :=
-- by library_search
not_imp_not.symm

-- 7ª demostración
example :
  (P → Q) ↔ (¬Q → ¬P) :=
-- by hint
by tauto

-- 8ª demostración
example :
  (P → Q) ↔ (¬Q → ¬P) :=
by finish
