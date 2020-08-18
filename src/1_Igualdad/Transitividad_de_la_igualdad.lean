-- Transitividad_de_la_igualdad.lean
-- Transitividad de la igualdad.
-- José A. Alonso Jiménez
-- Sevilla, 12 de agosto de 2020
-- ---------------------------------------------------------------------

-- En esta relación se muestra distintas pruebas de la transitividad de
-- la igualdad de los números reales: por reescritura, sustitución, con
-- lemas y automáticas.

-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la teoría de los números reales.
-- 2. Declarar x, y y z como variables sobre los números reales. 
-- ----------------------------------------------------------------------

import data.real.basic   -- 1
variables (x y z : ℝ)    -- 2

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la igualdad en los reales es transitiva; es
-- decir, si x, y y z son números reales tales que x = y e y = z,
-- entonces x = z.
-- ----------------------------------------------------------------------

-- 1ª demostración (con reescritura)
-- =================================

example 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
begin
  rw h,
  exact h',
end

-- Prueba:
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
-- + La táctica (rw h) cuando h es una igualdad sustituye en la
--   conclusión el término izquierdo de h por el derecho.
-- + La táctica (exact h) concluye la demostración si h es del tipo de
--   la conclusión.

-- 2ª demostración (con reescritura inversa)
-- =========================================

example 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
begin
  rw ← h',
  exact h,
end

-- Prueba:
/-
  x y z : ℝ,
  h : x = y,
  h' : y = z
  ⊢ x = z
rw ← h',
  ⊢ x = y
exact h,
  no goals
-/

-- Comentarios:
-- + La táctica (rw ← h) cuando h es una igualdad sustituye en la
--   conclusión el término derecho de h por el izquierdo

-- 3ª demostración (con reescritura en hipótesis)
-- ==============================================

example 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
begin
  rw h' at h,
  exact h,
end

-- Prueba:
/-
  x y z : ℝ,
  h : x = y,
  h' : y = z
  ⊢ x = z
rw h' at h,
  h : x = z
  ⊢ x = z
exact h,
  no goals
-/

-- Comentarios: 
-- + La táctica (rw h1 at h2) cuando h1 es una igualdad sustituye en la
--   hipótesis h2 el término izquierdo de h1 por el derecho.

-- 4ª demostración (con reescritura inversa en hipótesis)
-- ======================================================

example 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
begin
  rw ← h at h',
  exact h',
end

-- Prueba:
/-
  x y z : ℝ,
  h : x = y,
  h' : y = z
  ⊢ x = z
rw ← h at h',
  h' : x = z
  ⊢ x = z
exact h',
  no goals
-/

-- Comentarios: 
-- + La táctica (rw ← h1 at h2) cuando h1 es una igualdad sustituye en la
--   hipótesis h2 el término derecho de h1 por el izquierdo

-- 5ª demostración (con un lema)
-- =============================

example 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
eq.trans h h'

-- Comentarios:
-- + Se ha usado el lema
--   + eq.trans : a = b → b = c → a = c
-- + El lema se puede encontrar con
--      by suggest

-- 6ª demostración (por sustitución)
-- =================================

example 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
h' ▸ h

-- Comentario:
-- + Si h es una igualdad entonces h ▸ h' es la expresión obtenida sustituyendo
--   en h' el término izquierdo de h por el derecho. 

-- 7ª demostración (automática con linarith)
-- =========================================

example 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
by linarith

-- Comentarios:
-- + La táctica linarith demuestra la conclusión mediante aritmética
--   lineal. 
-- + La sugerencia de usar linarith se puede obtener escrbiendo 
--      by hint

-- 8ª demostración (automática con finish)
-- =======================================

example 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
by finish

-- Comentario: 
-- + La táctica finish demuestra la conclusión de forma automática.
-- + La sugerencia de usar finish se puede obtener escrbiendo 
--      by hint
