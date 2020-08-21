-- Monotonía de la suma por la derecha en Lean
-- ===========================================

-- Demostrar que si a, b y c son números reales 
-- tales que a ≤ b, entonces a + c ≤ b + c.

import data.real.basic

variables {a b c : ℝ}

-- 1ª demostración
example 
  (hab : a ≤ b) 
  : a + c ≤ b + c :=
begin
  rw ← sub_nonneg,
  have h : (b + c) - (a + c) = b - a, 
  { ring, },  
  { rw h, 
    rw sub_nonneg,
    exact hab, },
end

-- 2ª demostración
example 
  (hab : a ≤ b) 
  : a + c ≤ b + c :=
begin
  rw ← sub_nonneg,
  calc 
    0   ≤ b - a           
            : by exact sub_nonneg.mpr hab
    ... = b + c - (a + c) 
            : by exact (add_sub_add_right_eq_sub b a c).symm, 
end

-- 3ª demostración
example 
  (hab : a ≤ b) 
  : a + c ≤ b + c :=
begin
  rw ← sub_nonneg,
  calc 
    0   ≤ b - a           
            : sub_nonneg.mpr hab
    ... = b + c - (a + c) 
            : (add_sub_add_right_eq_sub b a c).symm, 
end

-- 4ª demostración
example 
  (hab : a ≤ b) 
  : a + c ≤ b + c :=
begin
  rw ← sub_nonneg,
  calc 0   ≤ b - a           : sub_nonneg.mpr hab
       ... = b + c - (a + c) : by ring,
end

-- 5ª demostración
example 
  (hab : a ≤ b) 
  : a + c ≤ b + c :=
begin
  rw ← sub_nonneg,
  simp,
  exact hab,
end

-- 6ª demostración
example 
  (hab : a ≤ b) 
  : a + c ≤ b + c :=
begin
  rw ← sub_nonneg,
  simp [hab],
end

-- 7ª demostración
example 
  (hab : a ≤ b) 
  : a + c ≤ b + c :=
begin
  simp [hab],
end

-- 8ª demostración
example 
  (hab : a ≤ b) 
  : a + c ≤ b + c :=
by simp [hab]

-- 9ª demostración
example 
  (hab : a ≤ b) 
  : a + c ≤ b + c :=
add_le_add_right hab c

-- 10ª demostración
example 
  (hab : a ≤ b) 
  : a + c ≤ b + c :=
by linarith

-- 11ª demostración
example 
  (hab : a ≤ b) 
  : a + c ≤ b + c :=
by finish

-- 12ª demostración
example 
  (hab : a ≤ b) 
  : a + c ≤ b + c :=
begin 
  rw add_comm a c,
  rw add_comm b c,
  exact add_le_add_left hab c,
end
