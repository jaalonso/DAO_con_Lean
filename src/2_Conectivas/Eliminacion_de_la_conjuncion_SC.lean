-- Eliminación de la conjunción en Lean
-- ====================================

-- Demostrar que
--    P ∧ Q → P

import tactic            
variables (P Q : Prop)   

-- 1ª demostración
example : P ∧ Q → P :=
begin
  intro h,
  cases h with hP hQ,
  exact hP,
end

-- 2ª demostración
example : P ∧ Q → P :=
begin
  rintro ⟨hP, hQ⟩,
  exact hP,
end

-- 3ª demostración
example : P ∧ Q → P :=
begin
  rintro ⟨hP, hQ⟩,
  assumption,
end

-- 4ª demostración
example : P ∧ Q → P :=
λ ⟨hP,_⟩, hP

-- 5ª demostración
example : P ∧ Q → P :=
begin
  assume h : P ∧ Q,
  show P, from h.1,
end

-- 6ª demostración
example : P ∧ Q → P :=
assume h, h.1

-- 7ª demostración
example : P ∧ Q → P :=
and.left

-- 8ª demostración
example : P ∧ Q → P :=
by tauto

-- 9ª demostración
example : P ∧ Q → P :=
by finish

