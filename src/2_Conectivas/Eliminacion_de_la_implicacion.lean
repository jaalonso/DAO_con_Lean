-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la librería de tácticas.
-- 2. Declarar P y Q como variables sobre proposiciones. 
-- ----------------------------------------------------------------------

import tactic            -- 1
variables (P Q : Prop)   -- 2

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si se tiene (P → Q) y P, entonces se tiene
-- Q. 
-- ----------------------------------------------------------------------

-- 1ª demostración (hacia atrás)
-- =============================

example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
begin
  apply h1,
  exact h2,
end 

-- Prueba:
/-
  P Q : Prop,
  h1 : P → Q,
  h2 : P
  ⊢ Q
apply h1,
  ⊢ P
exact h2,
  no goals
-/

-- 2ª demostración (hacia adelante)
-- ================================

example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
begin
  exact h1 h2,
end 

-- Comentarios:
-- + Si h1 es una demostración de (P → Q) y h2 es una demostración de P,
--   entonces (h1 h2) es una demostración de Q.

-- 3ª demostración (simplificació de la 2ª)
-- ========================================

example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
by exact h1 h2

-- 4ª demostración (mediante un término)
-- =====================================

example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
h1 h2

-- 5ª demostración (automática con tauto)
-- ======================================

example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
by tauto

-- Comentarios:
-- + La táctica tauto demuestra automáticamente las tautologías.

-- 6ª demostración (automática con finish)
-- =======================================

example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
by finish

-- 6ª demostración (automática con solve_by_elim)
-- ==============================================

example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
by solve_by_elim

-- Comentarios:
-- + La táctica solve_by_elim intnta demostrar el objetivo aplicándole
--   reglas de eliminación.
