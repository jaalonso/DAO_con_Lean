-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la igualdad en los reales es transitiva; es
-- decir, si x, y y z son números reales tales que x = y e y = z,
-- entonces x = z.
-- ----------------------------------------------------------------------

import data.real.basic

-- 1ª demostración
-- ===============

example 
  (x y z : ℝ) 
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

-- 2ª demostración
-- ===============

example 
  (x y z : ℝ) 
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

-- 3ª demostración
-- ===============

example 
  (x y z : ℝ) 
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

-- 4ª demostración
-- ===============

example 
  (x y z : ℝ) 
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

-- 5ª demostración
-- ===============

example 
  (x y z : ℝ) 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
eq.trans h h'

-- Comentarios:
-- + Se ha usado el lema
--   + eq.trans : a = b → b = c → a = c

-- Comprobación:
variables (a b c : ℝ)
#check @eq.trans ℝ a b c

-- 6ª demostración
-- ===============

example 
  (x y z : ℝ) 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
by linarith

-- Comentarios:
-- + La táctica linarith demuestra la conclusión mediante aritmética
--   lineal. 

-- 7ª demostración
-- ===============

example 
  (x y z : ℝ) 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
by finish

-- Comentario: 
-- + La táctica finish demuestra la conclusión de forma automática.
