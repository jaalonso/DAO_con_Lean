-- Monotonía de la multiplicación por no negativo
-- ==============================================

-- Demostrar que si a, b y c son números reales tales que 
-- 0 ≤ c y a ≤ b, entonces a*c ≤ b*c.

import data.real.basic

variables {a b c : ℝ}

-- 1ª demostración
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

-- 2ª demostración
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

-- 4ª demostración
example 
  (hc : 0 ≤ c) 
  (hab : a ≤ b) 
  : a * c ≤ b * c :=
begin
  rw ← sub_nonneg,
  calc 0 ≤ (b - a)*c  : mul_nonneg (by rwa sub_nonneg) hc
     ... =  b*c - a*c : by ring,
end

-- 5ª demostración
example 
  (hc : 0 ≤ c) 
  (hab : a ≤ b) 
  : a * c ≤ b * c :=
mul_mono_nonneg hc hab

-- 6ª demostración
example 
  (hc : 0 ≤ c) 
  (hab : a ≤ b) 
  : a * c ≤ b * c :=
by nlinarith


