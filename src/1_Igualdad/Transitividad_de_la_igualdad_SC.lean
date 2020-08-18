-- Transitividad de la igualdad en Lean
-- ====================================

-- Demostrar que si x, y y z son números reales tales que
-- x = y e y = z, entonces x = z.

import data.real.basic   

variables (x y z : ℝ)    

-- 1ª demostración
example 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
begin
  rw h,
  exact h',
end

-- 2ª demostración
example 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
begin
  rw ← h',
  exact h,
end

-- 3ª demostración
example 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
begin
  rw h' at h,
  exact h,
end

-- 4ª demostración
example 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
begin
  rw ← h at h',
  exact h',
end

-- 5ª demostración
example 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
eq.trans h h'

-- 6ª demostración
example 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
h' ▸ h

-- 7ª demostración
example 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
by linarith

-- 8ª demostración
example 
  (h : x = y) 
  (h' : y = z) 
  : x = z :=
by finish
