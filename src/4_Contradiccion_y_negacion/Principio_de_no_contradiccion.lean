-- Principio de no contradicción
-- =============================

import tactic

variable  (P : Prop)

-- ----------------------------------------------------
-- Ejercicio 1. Demostrar el principio de no contradicción
--    P ∧ ¬ P → false
-- ----------------------------------------------------

-- 1ª demostración
example : P ∧ ¬ P → false :=
begin
  intro h1,
  cases h1 with hP hnP,
  apply hnP,
  exact hP,
end

-- 2ª demostración
example : P ∧ ¬ P → false :=
begin
  rintro ⟨hP, hnP⟩,
  exact hnP hP,
end

-- 3ª demostración
example : P ∧ ¬ P → false :=
λ ⟨hP, hnP⟩, hnP hP

-- 4ª demostración
example : P ∧ ¬ P → false :=
-- by library_search
(and_not_self P).mp

-- 5ª demostración
example : P ∧ ¬ P → false :=
assume h : P ∧ ¬ P,
have hP : P,
  from and.elim_left h,
have hnP : ¬P,
  from and.elim_right h,
show false,
  from absurd hP hnP

-- 6ª demostración
example : P ∧ ¬ P → false :=
assume h : P ∧ ¬ P,
have hP : P,
  from and.left h,
have hnP : ¬P,
  from and.right h,
show false,
  from absurd hP hnP

-- 7ª demostración
example : P ∧ ¬ P → false :=
assume h : P ∧ ¬ P,
have hP : P,
  from h.left,
have hnP : ¬P,
  from h.right,
show false,
  from absurd hP hnP

-- 8ª demostración
example : P ∧ ¬ P → false :=
assume h : P ∧ ¬ P,
have hP : P,
  from h.1,
have hnP : ¬P,
  from h.2,
show false,
  from absurd hP hnP

-- 9ª demostración
example : P ∧ ¬ P → false :=
assume h : P ∧ ¬ P,
show false,
  from absurd h.1 h.2

-- 10ª demostración
example : P ∧ ¬ P → false :=
assume h : P ∧ ¬ P,
absurd h.1 h.2

-- 11ª demostración
example : P ∧ ¬ P → false :=
λ h, absurd h.1 h.2

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar el principio de no contradicción
--    P ∧ ¬ P → 0 = 1
-- ----------------------------------------------------

-- 1ª demostración
example : P ∧ ¬ P → 0 = 1 :=
begin
  rintro ⟨hP, hnP⟩,
  exfalso,
  exact hnP hP,
end

-- 2ª demostración
example : P ∧ ¬ P → 0 = 1 :=
λ h, absurd h.1 h.2
