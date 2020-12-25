-- Introducción de la implicación en Lean
-- ======================================

-- Demostrar que
--    P → P

import tactic
variables (P : Prop)

-- 1ª demostración
example : P → P :=
begin
  intro h,
  exact h,
end

-- 2ª demostración
example : P → P :=
λ h, h

-- 3ª demostración
example : P → P :=
id

-- 4ª demostración
example : P → P :=
begin
  assume h : P,
  show P, from h,
end

-- 5ª demostración
example : P → P :=
assume h, h

-- 6ª demostración
example : P → P :=
-- by hint
by tauto

-- 7ª demostración
example : P → P :=
by finish

-- 8ª demostración
example : P → P :=
by simp
