-- Monotonia_de_la_suma_por_la_izquierda.lean
-- Monotonía de la suma por la izquierda
-- José A. Alonso Jiménez
-- Sevilla, 14 de agosto de 2020
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a, b y c son números reles tales que 
-- a ≤ b, entonces c + a ≤ c + b.
--
-- Indicación: Se puede usar el lema
--    sub_nonneg : 0 ≤ a - b ↔ b ≤ a 
-- ----------------------------------------------------------------------

import data.real.basic
variables {a b c : ℝ}

-- 1ª demostración
-- ===============

example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
begin
  rw ← sub_nonneg,
  have h : (c + b) - (c + a) = b - a, 
  { ring, },  
  { rw h, 
    rw sub_nonneg,
    exact hab, },
end

-- Comentario: Se ha usado el lema
-- + sub_nonneg : 0 ≤ a - b ↔ b ≤ a 

-- 2ª demostración
-- ===============

example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
begin
  rw ← sub_nonneg,
  calc 0   ≤ b - a           : by exact sub_nonneg.mpr hab
       ... = c + b - (c + a) : by exact (add_sub_add_left_eq_sub b a c).symm, 
end

-- Comentario: Se usa el lema
-- + add_sub_add_left_eq_sub : c + a - (c + b) = a - b 

-- 3ª demostración
-- ===============

example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
begin
  rw ← sub_nonneg,
  calc 0   ≤ b - a           : sub_nonneg.mpr hab
       ... = c + b - (c + a) : (add_sub_add_left_eq_sub b a c).symm, 
end

-- 4ª demostración
-- ===============

example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
begin
  rw ← sub_nonneg,
  calc 0   ≤ b - a           : sub_nonneg.mpr hab
       ... = c + b - (c + a) : by ring
end

-- 5ª demostración
-- ===============

example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
begin
  rw ← sub_nonneg,
  simp,
  exact hab,
end

-- 6ª demostración
-- ===============

example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
begin
  rw ← sub_nonneg,
  simp [hab],
end

-- Comentario: 
-- + La táctica (simp [h]) aplica reglas de simplificación, ampliadas con
--   h, a la conclusión. 

-- 7ª demostración
-- ===============

example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
begin
  simp [hab],
end

-- 8ª demostración
-- ===============

example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
by simp [hab]

-- 9ª demostración
-- ===============

example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
add_le_add_left hab c

-- Comentario: Se ha usado el lema
-- + add_le_add_left : a ≤ b → ∀ (c : ℝ), c + a ≤ c + b 

-- 10ª demostración
-- ===============

example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
by linarith

-- 11ª demostración
-- ===============

example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
by finish
