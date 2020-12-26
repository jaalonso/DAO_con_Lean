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
  intro,
  have h : a * (1 - b) = 0,
    calc a * (1 - b)
         = a * 1 - a * b : mul_sub a 1 b
     ... = a - a * b     : by simp
     ... = 0             : by linarith,
  rw mul_eq_zero at h,
  cases h with ha hb,
    { left,
      exact ha, },
    { right,
      linarith, },
end

-- 2ª demostración
example :
  a = a * b → a = 0 ∨ b = 1 :=
begin
  intro,
  have h : a * (1 - b) = 0,
    { calc a * (1 - b)
           = a - a * b     : by ring
       ... = 0             : by linarith, },
  rw mul_eq_zero at h,
  cases h with ha hb,
    { left,
      exact ha, },
    { right,
      linarith, },
end

-- 3ª demostración
example :
  a = a * b → a = 0 ∨ b = 1 :=
begin
  intro,
  have h : a * (1 - b) = 0,
    { by linarith, },
  rw mul_eq_zero at h,
  cases h with ha hb,
    { left,
      exact ha, },
    { right,
      linarith, },
end

-- 4ª demostración
example :
  a = a * b → a = 0 ∨ b = 1 :=
begin
  intro,
  have h : a * (1 - b) = 0,
    by linarith,
  rw mul_eq_zero at h,
  cases h with ha hb,
    { left,
      exact ha, },
    { right,
      linarith, },
end

-- 5ª demostración
example :
  a = a * b → a = 0 ∨ b = 1 :=
assume : a = a * b,
have h1 : a * (1 - b) = 0,
  by linarith,
have h2 : a = 0 ∨ 1 - b = 0,
  from zero_eq_mul.mp (eq.symm h1),
or.elim h2
  ( assume h2a : a = 0,
    show a = 0 ∨ b = 1,
      from or.inl h2a)
  ( assume h2b : 1 - b = 0,
    have h3 : b = 1,
      from by linarith,
    show a = 0 ∨ b = 1,
      from or.inr h3)
