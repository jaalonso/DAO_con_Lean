-- Formulacion_equivalente_de_lema_con_dos_hipotesis.lean
-- Formulación equivalente de lemas con dos hipótesis.
-- José A. Alonso Jiménez
-- Sevilla, 24 de agosto de 2020
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (P ∧ Q → R) ↔ (P → (Q → R))
-- ----------------------------------------------------------------------

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
iff.intro (λ h ha hb, h ⟨ha, hb⟩) (λ h ⟨ha, hb⟩, h ha hb)

-- Comentario: Se ha usado el lema
-- + iff.intro : (P → Q) → (Q → P) → (P ↔ Q)

-- 3ª demostración
-- ===============

example : (P ∧ Q → R) ↔ (P → (Q → R)) :=
and_imp

-- Comentario: Se usa el lema
-- + and_imp : (P ∧ Q → R) ↔ (P → (Q → R))

-- 4ª demostración
-- ===============

example : (P ∧ Q → R) ↔ (P → (Q → R)) :=
by simp

-- 5ª demostración
-- ===============

example : (P ∧ Q → R) ↔ (P → (Q → R)) :=
by finish
