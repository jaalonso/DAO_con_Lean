-- Prueba mediante encadenamiento de ecuaciones
-- ============================================

-- Sean a, b y c números reales. Demostrar que
--    (a * b) * c = b * (a * c) 

import data.real.basic

variables (a b c : ℝ)

-- 1ª demostración
example : (a * b) * c = b * (a * c) :=
begin
  rw mul_comm a b,
  rw mul_assoc,
end

-- 2ª demostración
example : (a * b) * c = b * (a * c) :=
begin
  calc (a * b) * c = (b * a) * c : by rw mul_comm a b
              ...  = b * (a * c) : by rw mul_assoc,    
end

-- 3ª demostración
example : (a * b) * c = b * (a * c) :=
by linarith

-- 4ª demostración
example : (a * b) * c = b * (a * c) :=
by finish

-- 5ª demostración
example : (a * b) * c = b * (a * c) :=
by ring

