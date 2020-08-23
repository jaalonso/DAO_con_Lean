-- Monotonia_de_la_multiplicacion_por_no_positivo.lean
-- Monotonía de la multiplicación por no positivo.
-- José A. Alonso Jiménez
-- Sevilla, 22 de agosto de 2020
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a, b y c son números reales tales que 
-- c ≤ 0 y a ≤ b, entonces b*c ≤ a*c.
-- ----------------------------------------------------------------------

import data.real.basic

variables {a b c : ℝ}

-- 1ª demostración
-- ===============

example 
  (hc : c ≤ 0) 
  (hab : a ≤ b) 
  : b * c ≤ a * c :=
begin
  rw ← sub_nonneg,
  have h : a * c - b * c = (a - b) * c,
  { ring },
  { rw h,
    apply mul_nonneg_of_nonpos_of_nonpos,
    { rwa sub_nonpos, },
    { exact hc, }},
end

-- Comentario: Se ha usado los lemas
-- + mul_nonneg_of_nonpos_of_nonpos : a ≤ 0 → b ≤ 0 → 0 ≤ a * b
-- + sub_nonpos : a - b ≤ 0 ↔ a ≤ b

-- 2ª demostración
-- ===============

example 
  (hc : c ≤ 0) 
  (hab : a ≤ b) 
  : b * c ≤ a * c :=
begin
  have hab' : a - b ≤ 0,
  { rwa ← sub_nonpos at hab, },
  have h1 : 0 ≤ (a - b) * c,
  { exact mul_nonneg_of_nonpos_of_nonpos hab' hc, },
  have h2 : (a - b) * c = a * c - b * c,
  { ring, },
  have h3 : 0 ≤ a * c - b * c,
  { rwa h2 at h1, },
  rwa sub_nonneg at h3,
end

-- 3ª demostración
-- ===============

example 
  (hc : c ≤ 0) 
  (hab : a ≤ b) 
  : b * c ≤ a * c :=
begin
  rw ← sub_nonneg,
  have hab' : a - b ≤ 0,
  { rwa sub_nonpos, },
  calc 0 ≤ (a - b)*c  : mul_nonneg_of_nonpos_of_nonpos hab' hc
     ... =  a*c - b*c : by ring,
end

-- 4ª demostración
-- ===============

example 
  (hc : c ≤ 0) 
  (hab : a ≤ b) 
  : b * c ≤ a * c :=
mul_mono_nonpos hc hab

-- Comentario: Se usa el lema
-- + mul_mono_nonpos : 0 ≥ c → b ≤ a → a * c ≤ b * c

-- 5ª demostración
-- ===============

example 
  (hc : c ≤ 0) 
  (hab : a ≤ b) 
  : b * c ≤ a * c :=
by nlinarith

