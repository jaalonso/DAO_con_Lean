-- Eliminacion_de_la_conjuncion.lean
-- Eliminación de la conjunción.
-- José A. Alonso Jiménez
-- Sevilla, 12 de agosto de 2020
-- ---------------------------------------------------------------------

-- En este relación se muestra distintas formas de demostrar un teorema
-- con eliminación de la conjunción.

-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la librería de tácticas.
-- 2. Declarar P y Q como variables sobre proposiciones. 
-- ----------------------------------------------------------------------

import tactic            -- 1
variables (P Q : Prop)   -- 2

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    P ∧ Q → P
-- ----------------------------------------------------------------------

-- 1ª demostración (con intro, cases y exact)
-- ==========================================

example : P ∧ Q → P :=
begin
  intro h,
  cases h with hP hQ,
  exact hP,
end

-- Prueba:
/-
  P Q : Prop
  ⊢ P ∧ Q → P
intro h,
  h : P ∧ Q
  ⊢ P
cases h with hP hQ,
  hP : P,
  hQ : Q
  ⊢ P
exact hP,
  no goals
-/

-- Comentarios:
-- + La táctica (cases h with h1 h2), cuando la hipótesis h es una
--   conjunción aplica la regla de eliminación de la conjunción; es
--   decir, si h es (P ∧ Q), entonces elimina h y añade las hipótesis
--   (h1 : P) y (h2 : Q). 

-- 2ª demostración (con rintro y exact)
-- ====================================

example : P ∧ Q → P :=
begin
  rintro ⟨hP, hQ⟩,
  exact hP,
end

-- Prueba:
/-
  P Q : Prop
  ⊢ P ∧ Q → P
rintro ⟨hP, hQ⟩,
  hP : P,
  hQ : Q
  ⊢ P  
exact hP,
  no goals
-/

-- Comentarios:
-- + La táctica (rintro ⟨h1, h2⟩), cuando la conclusión es una
--   implicación cuyo antecedente es una conjunción, aplica las reglsa
--   de introducción de la implicación y de eliminación de la conjunción;
--   es decir, si la conclusión es (P ∧ Q → R) entonces añade las
--   hipótesis (h1 : P) y (h2 : Q) y cambia la conclusión a R.

-- 3ª demostración (con rintro y assumption)
-- =========================================

example : P ∧ Q → P :=
begin
  rintro ⟨hP, hQ⟩,
  assumption,
end

-- Comentarios:
-- + la táctica assumption concluye la demostración si la conclusión
--   coincide con alguna de las hipótesis.

-- 4ª demostración (estructurada)
-- ==============================

example : P ∧ Q → P :=
begin
  assume h : P ∧ Q,
  show P, from h.1,
end

-- 5ª demostración (estructurada)
-- ==============================

example : P ∧ Q → P :=
assume h, h.1

-- 6ª demostración (con término de prueba)
-- ======================================

example : P ∧ Q → P :=
λ ⟨hP,_⟩, hP

-- 7ª demostración (con lema)
-- ==========================

example : P ∧ Q → P :=
and.left

-- Comentarios: 
-- + Se usa el lema
--      and.left : P ∧ Q → P
-- + El lema se encuentra con
--      by library_search

-- 8ª demostración (automática con auto)
-- =====================================

example : P ∧ Q → P :=
by tauto

-- 9ª demostración (automática con finish)
-- =======================================

example : P ∧ Q → P :=
by finish

