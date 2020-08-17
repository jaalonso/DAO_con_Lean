-- Suma_con_no_negativo_es_mayor_o_igual.lean
-- Suma con no negativo es mayor o igual
-- José A. Alonso Jiménez
-- Sevilla, 14 de agosto de 2020
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar si a y b son números naturales y a es no
-- negativo, entonces b ≤ a + b
-- ----------------------------------------------------------------------

import data.real.basic
variables {a b : ℝ}

-- 1ª demostración
-- ===============

example  
  (ha : 0 ≤ a) 
  : b ≤ a + b :=
begin
  calc b = 0 + b : by rw zero_add
     ... ≤ a + b : by exact add_le_add_right ha b,
end

-- Comentario: Se ha usado el lema
-- + zero_add : 0 + a = a  

-- 2ª demostración
-- ===============

example  
  (ha : 0 ≤ a) 
  : b ≤ a + b :=
begin
  calc b = 0 + b : (zero_add b).symm
     ... ≤ a + b : add_le_add_right ha b,
end

-- 3ª demostración
-- ===============

example  
  (ha : 0 ≤ a) 
  : b ≤ a + b :=
begin
  calc b = 0 + b : by ring
     ... ≤ a + b : by exact add_le_add_right ha b,
end

-- 4ª demostración
-- ===============

example  
  (ha : 0 ≤ a) 
  : b ≤ a + b :=
by simp [ha]

-- 5ª demostración
-- ===============

example  
  (ha : 0 ≤ a) 
  : b ≤ a + b :=
by linarith

-- 6ª demostración
-- ===============

example  
  (ha : 0 ≤ a) 
  : b ≤ a + b :=
by finish

-- 7ª demostración
-- ===============

example  
  (ha : 0 ≤ a) 
  : b ≤ a + b :=
le_add_of_nonneg_left ha

-- Comentario: Se ha usado el lema
-- + le_add_of_nonneg_left : 0 ≤ b → a ≤ b + a 
