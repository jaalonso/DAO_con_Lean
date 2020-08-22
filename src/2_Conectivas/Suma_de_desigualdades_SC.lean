-- Suma de desigualdades (en Lean)
-- ===============================

-- Demostrar si a, b, c y d son números reales tales que
-- a ≤ b y c ≤ d, entonces a + c ≤ b + d.

import data.real.basic

variables (a b c d : ℝ)

-- 1ª demostración
example  
  (hab : a ≤ b) 
  (hcd : c ≤ d) 
  : a + c ≤ b + d :=
begin
  calc
    a + c ≤ b + c : add_le_add_right hab c
    ...   ≤ b + d : add_le_add_left hcd b,
end

-- 2ª demostración
example  
  (hab : a ≤ b) 
  (hcd : c ≤ d) 
  : a + c ≤ b + d :=
begin
  have h1 : a + c ≤ b + c := 
    add_le_add_right hab c,
  have h2 : b + c ≤ b + d :=
    add_le_add_left hcd b,
  show a + c ≤ b + d, 
    from le_trans h1 h2,
end

-- 3ª demostración
example  
  (hab : a ≤ b) 
  (hcd : c ≤ d) 
  : a + c ≤ b + d :=
add_le_add hab hcd

-- 4ª demostración
example  
  (hab : a ≤ b) 
  (hcd : c ≤ d) 
  : a + c ≤ b + d :=
by linarith


