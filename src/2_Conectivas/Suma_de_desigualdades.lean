-- Suma_de_desigualdades.lean
-- Suma de desigualdades
-- José A. Alonso Jiménez
-- Sevilla, 22 de agosto de 2020
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar si a, b, c y d son números reales tales que
-- a ≤ b y c ≤ d, entonces a + c ≤ b + d.
-- ----------------------------------------------------------------------

import data.real.basic

variables (a b c d : ℝ)

-- 1ª demostración
-- ===============

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
-- ===============

example  
  (hab : a ≤ b) 
  (hcd : c ≤ d) 
  : a + c ≤ b + d :=
add_le_add hab hcd

-- Comentario: Se ha usado el lema
-- + add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d 

-- 3ª demostración
-- ===============

example  
  (hab : a ≤ b) 
  (hcd : c ≤ d) 
  : a + c ≤ b + d :=
by linarith


