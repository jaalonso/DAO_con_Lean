-- Monotonía de la suma por la izquierda en Lean
-- =============================================

-- Demostrar que si a, b y c son números reales tales que 
-- a ≤ b, entonces c + a ≤ c + b.

import data.real.basic

variables {a b c : ℝ}

-- 1ª demostración
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

-- 2ª demostración
example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
begin
  rw ← sub_nonneg,
  calc 
    0   ≤ b - a           
            : by exact sub_nonneg.mpr hab
    ... = c + b - (c + a) 
            : by exact (add_sub_add_left_eq_sub b a c).symm, 
end

-- 3ª demostración
example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
begin
  rw ← sub_nonneg,
  calc 
  0   ≤ b - a           
          : sub_nonneg.mpr hab
  ... = c + b - (c + a) 
          : (add_sub_add_left_eq_sub b a c).symm,
end

-- 4ª demostración
example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
begin
  rw ← sub_nonneg,
  calc 0   ≤ b - a           : sub_nonneg.mpr hab
       ... = c + b - (c + a) : by ring
end

-- 5ª demostración
example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
begin
  rw ← sub_nonneg,
  simp,
  exact hab,
end

-- 6ª demostración
example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
begin
  rw ← sub_nonneg,
  simp [hab],
end

-- 7ª demostración
example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
begin
  simp [hab],
end

-- 8ª demostración
example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
by simp [hab]

-- 9ª demostración
example 
  (d : ℝ)
  (hab : a ≤ b) 
  : d + a ≤ d + b :=
add_le_add_left hab d

-- 10ª demostración
example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
by linarith

-- 11ª demostración
example 
  (hab : a ≤ b) 
  : c + a ≤ c + b :=
by finish
