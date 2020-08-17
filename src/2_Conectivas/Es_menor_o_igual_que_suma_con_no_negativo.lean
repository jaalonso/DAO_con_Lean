-- Es_menor_o_igual_que_suma_con_no_negativo.lean
-- Es menor o igual que suma con no negativo
-- José A. Alonso Jiménez
-- Sevilla, 14 de agosto de 2020
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar si a y b son números naturales y b es no
-- negativo, entonces a ≤ a + b
-- ----------------------------------------------------------------------

import data.real.basic
variables {a b : ℝ}

-- 1ª demostración
-- ===============

example  
  (hb : 0 ≤ b) 
  : a ≤ a + b :=
begin
  calc a = a + 0 : by rw add_zero
     ... ≤ a + b : by exact add_le_add_left hb a,
end

-- Comentario: Se ha usado el lema
-- + add_le_add_left : a ≤ b → ∀ (c : ℝ), c + a ≤ c + b 

-- 2ª demostración
-- ===============

example  
  (hb : 0 ≤ b) 
  : a ≤ a + b :=
begin
  calc a = a + 0 : (add_zero a).symm
     ... ≤ a + b : add_le_add_left hb a,
end

-- 3ª demostración
-- ===============

example  
  (hb : 0 ≤ b) 
  : a ≤ a + b :=
begin
  calc a = a + 0 : by ring
     ... ≤ a + b : add_le_add_left hb a,
end

-- 4ª demostración
-- ===============

example  
  (hb : 0 ≤ b) 
  : a ≤ a + b :=
by simp [hb]

-- 5ª demostración
-- ===============

example  
  (hb : 0 ≤ b) 
  : a ≤ a + b :=
by linarith

-- 6ª demostración
-- ===============

example  
  (hb : 0 ≤ b) 
  : a ≤ a + b :=
by finish

-- 7ª demostración
-- ===============

example  
  (hb : 0 ≤ b) 
  : a ≤ a + b :=
le_add_of_nonneg_right hb

-- Comentario: Se usa el lema
-- + le_add_of_nonneg_right : 0 ≤ b → a ≤ a + b 
