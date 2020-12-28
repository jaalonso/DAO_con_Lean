-- Propiedad: ∀ a b : ℝ, a = a * b → a = 0 ∨ b = 1
-- ===============================================

import data.real.basic

variables (a b : ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Demostrar que para todo a y b, números
-- reales, se tiene
--    a = a * b → a = 0 ∨ b = 1
-- ----------------------------------------------------

-- 1ª demostración
example :
  a = a * b → a = 0 ∨ b = 1 :=
begin
  intro h1,
  have h2 : a * (1 - b) = 0,
    calc a * (1 - b)
         = a * 1 - a * b : mul_sub a 1 b
     ... = a - a * b     : by simp
     ... = 0             : by linarith,
  rw mul_eq_zero at h2,
  cases h2 with ha hb,
    { left,
      exact ha, },
    { right,
      linarith, },
end

-- 2ª demostración
example :
  a = a * b → a = 0 ∨ b = 1 :=
begin
  intro h1,
  have h2 : a * (1 - b) = 0,
    { calc a * (1 - b)
           = a - a * b     : by ring
       ... = 0             : by linarith, },
  rw mul_eq_zero at h2,
  cases h2 with ha hb,
    { left,
      exact ha, },
    { right,
      linarith, },
end

-- 3ª demostración
example :
  a = a * b → a = 0 ∨ b = 1 :=
begin
  intro h1,
  have h2 : a * (1 - b) = 0,
    { by linarith, },
  rw mul_eq_zero at h2,
  cases h2 with ha hb,
    { left,
      exact ha, },
    { right,
      linarith, },
end

-- 4ª demostración
example :
  a = a * b → a = 0 ∨ b = 1 :=
assume h1: a = a * b,
have h2 : a * (1 - b) = 0,
  by linarith,
have h3 : a = 0 ∨ 1 - b = 0,
  from zero_eq_mul.mp (eq.symm h2),
or.elim h3
  ( assume h3a : a = 0,
    show a = 0 ∨ b = 1,
      from or.inl h3a)
  ( assume h3b : 1 - b = 0,
    have h4 : b = 1,
      from by linarith,
    show a = 0 ∨ b = 1,
      from or.inr h4)
