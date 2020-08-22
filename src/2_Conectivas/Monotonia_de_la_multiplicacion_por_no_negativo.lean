-- Monotonia_de_la_multiplicacion_por_no_negativo.lean
-- Monotonía de la multiplicación por no negativo.
-- José A. Alonso Jiménez
-- Sevilla, 22 de agosto de 2020
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a, b y c son números reales tales que 
-- 0 ≤ c y a ≤ b, entonces a*c ≤ b*c.
-- ----------------------------------------------------------------------

import data.real.basic

variables {a b c : ℝ}

-- 1ª demostración
-- ===============

example 
  (hc : 0 ≤ c) 
  (hab : a ≤ b) 
  : a * c ≤ b * c :=
begin
  rw ← sub_nonneg,
  have h : b * c - a * c = (b - a) * c,
  { ring },
  { rw h,
    apply mul_nonneg,
    { rw sub_nonneg,
      exact hab },
    { exact hc }},
end

-- Comentario: Se ha usado el lema
-- + mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b

-- 2ª demostración
-- ===============

example 
  (hc : 0 ≤ c) 
  (hab : a ≤ b) 
  : a * c ≤ b * c :=
begin
  have hab' : 0 ≤ b - a,
  { rw ← sub_nonneg at hab,
    exact hab, },
  have h1 : 0 ≤ (b - a) * c,
  { exact mul_nonneg hab' hc, },
  have h2 : (b - a) * c = b * c - a * c,
  { ring, },
  have h3 : 0 ≤ b * c - a * c,
  { rw h2 at h1,
    exact h1, },
  rw sub_nonneg at h3,
  exact h3,
end

-- 3ª demostración
-- ===============

example 
  (hc : 0 ≤ c) 
  (hab : a ≤ b) 
  : a * c ≤ b * c :=
begin
  have hab' : 0 ≤ b - a,
  { rwa ← sub_nonneg at hab, },
  have h1 : 0 ≤ (b - a) * c,
  { exact mul_nonneg hab' hc },
  have h2 : (b - a) * c = b * c - a * c,
  { ring, },
  have h3 : 0 ≤ b * c - a * c,
  { rwa h2 at h1, },
  rwa sub_nonneg at h3,
end

-- Comentario: 
-- + La táctica (rwa h at h'), cuando h es una igualdad. sustituye en la
--   hipótesis h' el término izquierdo de h por el derecho y, a
--   continuación, aplica assumption.
-- + La táctica (rwa ← h at h'), cuando h es una igualdad, sustituye en
--   la hipótesis h' el término derecho de h por el izquierdo y, a
--   continuación, aplica assumption.

-- 4ª demostración
-- ===============

example 
  (hc : 0 ≤ c) 
  (hab : a ≤ b) 
  : a * c ≤ b * c :=
mul_mono_nonneg hc hab

-- Comentario: Se usa el lema
-- + mul_mono_nonneg : 0 ≤ c → a ≤ b → a * c ≤ b * c 

-- 5ª demostración
-- ===============

example 
  (hc : 0 ≤ c) 
  (hab : a ≤ b) 
  : a * c ≤ b * c :=
by nlinarith

-- Comentario: 
-- + La táctica nlinarith es una extensión de linarith con un
--   preprocesamiento que permite resolver problemas aritméticos no
--   lineales.  
