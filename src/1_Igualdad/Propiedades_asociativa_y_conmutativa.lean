-- ---------------------------------------------------------------------
-- Ejercicio. Sean a, b y c números reales. Demostrar que
--    (a * b) * c = b * (a * c) 
-- ----------------------------------------------------------------------

import data.real.basic

variables (a b c : ℝ)

-- 1ª demostración
-- ===============

example : (a * b) * c = b * (a * c) :=
begin
  rw mul_comm a b,
  rw mul_assoc,
end

-- Prueba:
/-
  a b c : ℝ
  ⊢ (a * b) * c = b * (a * c)
rw mul_comm a b,
  ⊢ (b * a) * c = b * (a * c)
rw mul_assoc,
  no goals
-/

-- Comentarios:
-- + Se han usado los lemas
--   + mul_comm : ∀ (a b : ℝ), a * b = b * a 
--   + mul_assoc : ∀ (a b c : ℝ), a * b * c = a * (b * c)   

-- 2ª demostración
-- ===============

example : (a * b) * c = b * (a * c) :=
by linarith

-- 3ª demostración
-- ===============

example : (a * b) * c = b * (a * c) :=
by ring

-- Comentarios:
-- + La táctica ring demuestra la conclusión normalizando las
--   expresiones con las regñlas de los anillos.

-- 4ª demostración
-- ===============

example : (a * b) * c = b * (a * c) :=
by finish
