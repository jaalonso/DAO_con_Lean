-- Prueba con hipótesis y uso de lemas
-- ===================================

-- Sean a, b, c y d números reales. Demostrar que si 
--    c = d * a + b  
--    b = a + d
-- entonces c = 2 * a * d. 

import data.real.basic

variables (a b c d : ℝ)

-- 1ª demostración
example 
  (h1 : c = d * a + b) 
  (h2 : b = a * d) 
  : c = 2 * a * d :=
begin
  rw h2 at h1,
  rw mul_comm at h1,
  rw ← two_mul (a * d) at h1,
  rw ← mul_assoc at h1,
  exact h1,
end

-- 2ª demostración
example 
  (h1 : c = d * a + b) 
  (h2 : b = a * d) 
  : c = 2 * a * d :=
begin
  calc
    c   = d * a + b     : by exact h1 
    ... = d * a + a * d : by rw h2 
    ... = a * d + a * d : by rw mul_comm 
    ... = 2 * (a * d)   : by rw two_mul (a * d) 
    ... = 2 * a * d     : by rw mul_assoc,
end

-- 3ª demostración
example 
  (h1 : c = d * a + b) 
  (h2 : b = a * d) 
  : c = 2 * a * d :=
begin
  calc
    c   = d * a + b     : by exact h1 
    ... = d * a + a * d : by rw h2
    ... = 2 * a * d     : by ring,
end

-- 4ª demostración
example 
  (h1 : c = d * a + b) 
  (h2 : b = a * d) 
  : c = 2 * a * d :=
by linarith
