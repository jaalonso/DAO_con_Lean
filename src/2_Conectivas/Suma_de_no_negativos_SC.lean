-- Suma de no negativos (en Lean)
-- ==============================

-- Demostrar si a y b son números reales no negativos, 
-- entonces a + b es no negativo.

import data.real.basic

variables (a b : ℝ)

-- 1ª demostración
example  
  (ha : 0 ≤ a) 
  (hb : 0 ≤ b) 
  : 0 ≤ a + b :=
begin
  calc 0 ≤ a     : ha
     ... ≤ a + b : le_add_of_nonneg_right hb,
end

-- 2ª demostración
example  
  (ha : 0 ≤ a) 
  (hb : 0 ≤ b) 
  : 0 ≤ a + b :=
add_nonneg ha hb

-- 3ª demostración
example  
  (ha : 0 ≤ a) 
  (hb : 0 ≤ b) 
  : 0 ≤ a + b :=
by linarith

