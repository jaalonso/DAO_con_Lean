-- Formulación equivalente de lemas con dos hipótesis
-- ==================================================

-- Demostrar que
--    (P ∧ Q → R) ↔ (P → (Q → R))

import tactic

variables (P Q R : Prop)

-- 1ª demostración
-- ===============

example : (P ∧ Q → R) ↔ (P → (Q → R)) :=
begin
  split,
  { intros h hP hQ,
    exact h ⟨hP, hQ⟩, },
  { rintro h ⟨hP, hQ⟩,
    exact h hP hQ, },
end

-- 2ª demostración
-- ===============

example : (P ∧ Q → R) ↔ (P → (Q → R)) :=
iff.intro (λ h hP hQ, h ⟨hP, hQ⟩) 
          (λ h ⟨hP, hQ⟩, h hP hQ)

-- 3ª demostración
-- ===============

example : (P ∧ Q → R) ↔ (P → (Q → R)) :=
and_imp

-- 4ª demostración
-- ===============

example : (P ∧ Q → R) ↔ (P → (Q → R)) :=
by simp

-- 5ª demostración
-- ===============

example : (P ∧ Q → R) ↔ (P → (Q → R)) :=
by finish
