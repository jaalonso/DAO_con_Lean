-- Conmutatividad de la conjunción
-- ===============================

-- Demostrar que
--    P ∧ Q → Q ∧ P

import tactic            

variables (P Q R : Prop)

-- 1ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
begin
  intro h,
  cases h with hP hQ,
  split,
  { exact hQ },
  { exact hP },
end

-- 2ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
begin
  rintro ⟨hP, hQ⟩,
  exact ⟨hQ, hP⟩,
end

-- 3ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
λ ⟨hP, hQ⟩, ⟨hQ, hP⟩

-- 4ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
and.comm.mp

-- 5ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
by tauto

-- 6ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
by finish


