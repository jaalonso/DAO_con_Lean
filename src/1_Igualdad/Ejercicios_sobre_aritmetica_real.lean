-- ---------------------------------------------------------------------
-- Ejercicio 1. Ejecutar las siguientes acciones:
-- 1. Importar la teoría de los números reales.
-- 2. Declarar a, b, c y d como variables sobre los reales. 
-- ----------------------------------------------------------------------

import data.real.basic     -- 1
variables (a b c d : ℝ)    -- 2

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    (c * b) * a = b * (a * c)
--
-- Indicación: Para alguna pueba pueden ser útiles los lemas
-- + mul_assoc : (a * b) * c = a * (b * c)   
-- + mul_comm  : a * b = b * a 
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : (c * b) * a = b * (a * c) :=
begin
  rw mul_comm c b,
  rw mul_assoc,
  rw mul_comm c a,
end

-- Prueba:
/-
  a b c : ℝ
  ⊢ (c * b) * a = b * (a * c)
rw mul_comm c b,
  ⊢ (b * c) * a = b * (a * c)
rw mul_assoc,
  ⊢ b * (c * a) = b * (a * c)
rw mul_comm c a,
  no goals
-/

-- 2ª demostración
-- ===============

example : (c * b) * a = b * (a * c) :=
begin
  calc (c * b) * a = (b * c) * a : by rw mul_comm c b
               ... = b * (c * a) : by rw mul_assoc
               ... = b * (a * c) : by rw mul_comm c a,
end

-- 3ª demostración
-- ===============

example : (c * b) * a = b * (a * c) :=
by linarith

-- 4ª demostración
-- ===============

example : (c * b) * a = b * (a * c) :=
by finish

-- 5ª demostración
-- ===============

example : (c * b) * a = b * (a * c) :=
by ring

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si
--    c = b * a - d 
--    d = a * b
-- entonces c = 0.
-- 
-- Indicación: Para alguna pueba pueden ser útiles los lemas
-- + mul_comm : a * b = b * a 
-- + sub_self : a - a = 0
-- ----------------------------------------------------------------------

example
  (h1 : c = b * a - d) 
  (h2 : d = a * b) 
  : c = 0 :=
begin
  rw h2 at h1,
  rw mul_comm b a at h1,
  rw sub_self (a * b) at h1,
  exact h1,
end

-- Prueba:
/-
  a b c d : ℝ,
  h1 : c = b * a - d,
  h2 : d = a * b
  ⊢ c = 0
rw h2 at h1,
  h1 : c = b * a - a * b
  ⊢ c = 0
rw mul_comm b a at h1,
  h1 : c = a * b - a * b
  ⊢ c = 0
rw sub_self (a * b) at h1,
  h1 : c = 0
  ⊢ c = 0
exact h1,
  no goals
-/

-- 2ª demostración
-- ===============

example 
  (h1 : c = b * a - d) 
  (h2 : d = a * b) 
  : c = 0 :=
begin
  calc c = b * a - d     : by rw h1
     ... = b * a - a * b : by rw h2 
     ... = a * b - a * b : by rw mul_comm a b
     ... = 0             : by rw sub_self (a*b),
end

-- 3ª demostración
-- ===============

example 
  (h1 : c = b * a - d) 
  (h2 : d = a * b) 
  : c = 0 :=
begin
  calc c = b * a - d     : by rw h1
     ... = b * a - a * b : by rw h2 
     ... = 0             : by ring,
end

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que
--    (a + b) + a = 2 * a + b
-- 
-- Indicación: Para alguna pueba pueden ser útiles los lemas
-- + add_assoc : (a + b) + c = a + (b + c) 
-- + add_comm  : a + b = b + a 
-- + two_mul   : 2 * a = a + a
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : (a + b) + a = 2 * a + b :=
begin
  calc (a + b) + a = a + (b + a) : by rw add_assoc
               ... = a + (a + b) : by rw add_comm b a
               ... = (a + a) + b : by rw ← add_assoc
               ... = 2 * a + b   : by rw two_mul,
end

-- 2ª demostración
-- ===============

example : (a + b) + a = 2 * a + b :=
by ring

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que
--    (a + b) * (a - b) = a^2 - b^2
-- 
-- Indicación: Para alguna pueba pueden ser útiles los lemas
-- + add_mul  : (a + b) * c = a * c + b * c 
-- + add_sub  : a + (b - c) = (a + b) - c
-- + add_zero : a + 0 = a
-- + mul_comm : a * b = b * a 
-- + mul_sub  : a * (b - c) = a * b - a * c 
-- + pow_two  : a^2 = a * a
-- + sub_self : a - a = 0
-- + sub_sub  : (a - b) - c = a - (b + c)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : (a + b) * (a - b) = a^2 - b^2 :=
begin
  rw pow_two a,
  rw pow_two b,
  rw mul_sub (a + b) a b,
  rw add_mul a b a,
  rw add_mul a b b,
  rw mul_comm b a,
  rw ← sub_sub,
  rw ← add_sub,
  rw sub_self,
  rw add_zero,
end

-- Prueba:
/-
  a b : ℝ
  ⊢ (a + b) * (a - b) = a ^ 2 - b ^ 2
rw pow_two a,
  ⊢ (a + b) * (a - b) = a * a - b ^ 2
rw pow_two b,
  ⊢ (a + b) * (a - b) = a * a - b * b
rw mul_sub (a + b) a b,
  ⊢ (a + b) * a - (a + b) * b = a * a - b * b
rw add_mul a b a,
  ⊢ a * a + b * a - (a + b) * b = a * a - b * b
rw add_mul a b b,
  ⊢ a * a + b * a - (a * b + b * b) = a * a - b * b
rw mul_comm b a,
  ⊢ a * a + a * b - (a * b + b * b) = a * a - b * b
rw ← sub_sub,
  ⊢ a * a + a * b - a * b - b * b = a * a - b * b
rw ← add_sub,
  ⊢ a * a + (a * b - a * b) - b * b = a * a - b * b
rw sub_self,
  ⊢ a * a + 0 - b * b = a * a - b * b
rw add_zero,
  no goals
-/

-- 2ª demostración
-- ===============

example : (a + b) * (a - b) = a^2 - b^2 :=
begin
  calc (a + b) * (a - b) 
           = (a + b) * a - (a + b) * b       : by rw mul_sub (a + b) a b
       ... = a * a + b * a - (a + b) * b     : by rw add_mul a b a
       ... = a * a + b * a - (a * b + b * b) : by rw add_mul a b b
       ... = a * a + a * b - (a * b + b * b) : by rw mul_comm b a
       ... = a * a + a * b - a * b - b * b   : by rw sub_sub
       ... = a * a + (a * b - a * b) - b * b : by rw add_sub
       ... = a * a + 0 - b * b               : by rw sub_self
       ... = a * a - b * b                   : by rw add_zero
       ... = a^2 - b * b                     : by rw pow_two a
       ... = a^2 - b^2                       : by rw pow_two b,
end

-- 3ª demostración
-- ===============

example : (a + b) * (a - b) = a^2 - b^2 :=
by ring

