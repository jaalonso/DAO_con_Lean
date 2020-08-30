-- Conmutatividad_de_la_conjuncion.lean
-- Conmutatividad de la conjunción
-- José A. Alonso Jiménez
-- Sevilla, 23 de agosto de 2020
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    P ∧ Q → Q ∧ P
-- ----------------------------------------------------------------------

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

-- Comentarios:
-- 1. Se usa el lema 
--    + and.comm : P ∧ Q ↔ Q ∧ P
-- 2. Si h es una equivalencia (P ↔ Q, entonces h.mp es (P → Q).
-- 3. Si h es una equivalencia (P ↔ Q, entonces h.mpr es (Q → P).

-- 5ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
begin
  assume h : P ∧ Q,
  have hP : P := h.left,
  have hQ : Q := h.right,
  show Q ∧ P, from ⟨hQ, hP⟩,
end

-- 6ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
begin
  assume h : P ∧ Q,
  show Q ∧ P, from ⟨h.right, h.left⟩,
end

example : P ∧ Q → Q ∧ P :=
begin
  assume h : P ∧ Q,
  show Q ∧ P, from ⟨h.2, h.1⟩,
end

-- 7ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
λ h, ⟨h.2, h.1⟩

-- 8ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
by tauto

-- 9ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
by finish
