-- Propiedad: ∀ x : ℝ, x^2 = 1 → x = 1 ∨ x = -1
-- ============================================

import data.real.basic

variables (x : ℝ)

-- -----------------------------------------------------
-- Ejercicio 1. Demostrar que si
--    x^2 = 1
-- entonces
--    x = 1 ∨ x = -1
-- -----------------------------------------------------

-- 1ª demostración
example
  (h : x^2 = 1)
  : x = 1 ∨ x = -1 :=
begin
  have h1 : (x - 1) * (x + 1) = 0,
    calc (x - 1) * (x + 1)
         = x^2 - 1         : by ring
     ... = 1 - 1           : by rw h
     ... = 0               : by ring,
  have h2 : x - 1 = 0 ∨ x + 1 = 0,
    { -- by suggest,
      exact mul_eq_zero.mp h1 },
  cases h2 with h2a h2b,
    { left,
      -- by suggest,
      exact sub_eq_zero.mp h2a, },
    { right,
      -- by library_search,
      exact eq_neg_of_add_eq_zero h2b, },
end

-- 2ª demostración
example
  (h : x^2 = 1)
  : x = 1 ∨ x = -1 :=
begin
  have h1 : (x - 1) * (x + 1) = 0,
    linarith,
  have h2 : x - 1 = 0 ∨ x + 1 = 0,
    finish,
  cases h2 with h2a h2b,
    { left,
      linarith, },
    { right,
      linarith, },
end

-- 3ª demostración
example
  (h : x^2 = 1)
  : x = 1 ∨ x = -1 :=
have h1 : (x - 1) * (x + 1) = 0, from
  calc (x - 1) * (x + 1)
       = x^2 - 1         : by ring
   ... = 1 - 1           : by rw h
   ... = 0               : by ring,
have h2 : x - 1 = 0 ∨ x + 1 = 0,
  from mul_eq_zero.mp h1,
or.elim h2
  ( assume h2a : x - 1 = 0,
    have h3 : x = 1,
      from sub_eq_zero.mp h2a,
    show x = 1 ∨ x = -1,
      from or.inl h3)
  ( assume h2b : x + 1 = 0,
    have h4 : x = -1,
      from eq_neg_of_add_eq_zero h2b,
    show x = 1 ∨ x = -1,
      from or.inr h4)

-- 4ª demostración
example
  (h : x^2 = 1)
  : x = 1 ∨ x = -1 :=
have h1 : (x - 1) * (x + 1) = 0,
  by linarith,
have h2 : x - 1 = 0 ∨ x + 1 = 0,
  by finish,
or.elim h2
  ( assume h2a : x - 1 = 0,
    have h3 : x = 1,
      by linarith,
    show x = 1 ∨ x = -1,
      from or.inl h3)
  ( assume h2b : x + 1 = 0,
    have h4 : x = -1,
      by linarith,
    show x = 1 ∨ x = -1,
      from or.inr h4)
