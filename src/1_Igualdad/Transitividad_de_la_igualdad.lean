-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la igualdad en los reales es transitiva; es
-- decir, si x, y y z son números reales tales que x = y e y = z,
-- entonces x = z.
-- ----------------------------------------------------------------------

import data.real.basic

example 
  (x y z : ℝ) 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
begin
  rw h,
  exact h',
end

-- Prueba
-- ======

/-
  x y z : ℝ,
  h : x = y,
  h' : y = z
  ⊢ x = z
rw h,
  ⊢ y = z
exact h',
  no goals
-/

-- Comentarios:
-- 1. La táctica (rw h) cuando h es una igualdad sustituye en la
--    conclusión el término izquierdo de h por el derecho.
-- 2. La táctica (exact h) concluye la demostración si h es del tipo de
--    la conclusión.
