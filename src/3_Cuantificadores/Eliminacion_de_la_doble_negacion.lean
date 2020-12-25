-- Eliminación de la doble negación
-- ================================

-- ----------------------------------------------------
-- Ejercicio. Demostrar
--     P ∨ ¬ P ⊢ ¬¬P → P
-- ----------------------------------------------------

import tactic

variable (P : Prop)

-- 1ª demostración
example
  (h : P ∨ ¬ P)
  : ¬¬P → P :=
begin
  intro hnnP,
  cases h with hP hnP,
  { exact hP, },
  { exfalso,
    apply hnnP,
    exact hnP, },
end

-- 2ª demostración
example
  (h : P ∨ ¬ P)
  : ¬¬P → P :=
begin
  intro hnnP,
  cases h with hP hnP,
  { exact hP, },
  { exfalso,
    exact hnnP hnP, },
end

-- 3ª demostración
example
  (h : P ∨ ¬ P)
  : ¬¬P → P :=
assume hnnP : ¬¬P ,
or.elim h
  ( assume hP : P,
    show P,
      from hP)
  ( assume hnP : ¬P,
    show P,
      from absurd hnP hnnP)

-- 4ª demostración
example
  (h : P ∨ ¬ P)
  : ¬¬P → P :=
assume hnnP : ¬¬P ,
or.elim h
  (λ hP, hP)
  (λ hnP, absurd hnP hnnP)

-- 5ª demostración
example
  (h : P ∨ ¬ P)
  : ¬¬P → P :=
λ hnnP, or.elim h id (λ hnP, absurd hnP hnnP)

-- 6ª demostración
example
  (h : P ∨ ¬ P)
  : ¬¬P → P :=
-- by library_search
or.resolve_right h

-- 7ª demostración
example
  (h : P ∨ ¬ P)
  : ¬¬P → P :=
-- by hint
by tauto

-- 8ª demostración
example
  (h : P ∨ ¬ P)
  : ¬¬P → P :=
by finish

-- 9ª demostración
example
  (h : P ∨ ¬ P)
  : ¬¬P → P :=
by simp
