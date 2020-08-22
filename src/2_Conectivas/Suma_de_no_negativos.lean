-- Suma_de_no_negativos.lean
-- Suma de no negativos.
-- José A. Alonso Jiménez
-- Sevilla, 22 de agosto de 2020
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 1.. Demostrar si a y b son números reales no negativos, 
-- entonces a + b es no negativo.
-- ----------------------------------------------------------------------

import data.real.basic

variables (a b : ℝ)

-- 1ª demostración
-- ===============

example  
  (ha : 0 ≤ a) 
  (hb : 0 ≤ b) 
  : 0 ≤ a + b :=
begin
  calc 0 ≤ a     : ha
     ... ≤ a + b : le_add_of_nonneg_right hb,
end

-- 2ª demostración
-- ===============

example  
  (ha : 0 ≤ a) 
  (hb : 0 ≤ b) 
  : 0 ≤ a + b :=
add_nonneg ha hb

-- Comentario: Se usa el lema
-- + add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b

-- 3ª demostración
-- ===============

example  
  (ha : 0 ≤ a) 
  (hb : 0 ≤ b) 
  : 0 ≤ a + b :=
by linarith

