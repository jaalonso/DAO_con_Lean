-- Monotonía de la multiplicación por no positivo
-- ==============================================

-- Demostrar que si a, b y c son números reales tales que 
-- c ≤ 0 y a ≤ b, entonces b*c ≤ a*c.

import data.real.basic

variables {a b c : ℝ}

-- 1ª demostración
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

-- 2ª demostración
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
example 
  (hc : c ≤ 0) 
  (hab : a ≤ b) 
  : b * c ≤ a * c :=
mul_mono_nonpos hc hab

-- 5ª demostración
example 
  (hc : c ≤ 0) 
  (hab : a ≤ b) 
  : b * c ≤ a * c :=
by nlinarith

