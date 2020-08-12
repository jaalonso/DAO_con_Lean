-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la librería de tácticas.
-- 2. Declarar P como variable sobre proposiciones. 
-- ----------------------------------------------------------------------

import tactic          -- 1
variables (P : Prop)   -- 2

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    P → P
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : P → P :=
begin
  intro h,
  exact h,
end

-- Prueba:
/-
  P : Prop
  ⊢ P → P
intro h,
  h : P
  ⊢ P
exact h,
  no goals
-/

-- Comentarios:
-- + La táctica (intro h), cuando la conclusión es una implicación,
--   aplica la regla de introducción de la implicación; es decir, si la
--   conclusión es (P → Q) entonces añade la hipótesis (h : P) y cambia
--   la conclusión a Q.

-- 3ª demostración (por un término)
-- ================================

example : P → P :=
λ h, h

-- 4ª demostración (mediante id)
-- =============================

example : P → P :=
id

-- Comentario: Se usa el lema
-- + id : P → P

-- 5ª demostración (estructurada)
-- ==============================

example : P → P :=
begin
  assume h : P,
  show P, from h,
end  

-- 6ª demostración (automática con tauto)
-- ======================================

example : P → P :=
by tauto

-- 7ª demostración (automática con finish)
-- =======================================

example : P → P :=
by finish

-- 8ª demostración (por simplificación)
-- ====================================

example : P → P :=
by simp

-- Comentarios:
-- + La táctica simp aplica reglas de simplificación a la conclusión.

