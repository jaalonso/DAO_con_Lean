-- Propiedad: ∀ x y : ℝ, x^2 = y^2 → x = y ∨ x = -y
-- ================================================

import data.real.basic

variables (x y : ℝ)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar si
--    x^2 = y^2
-- entonces
--    x = y ∨ x = -y
-- ----------------------------------------------------------------------

-- 1ª demostración
example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
begin
  have h1 : (x - y) * (x + y) = 0,
    calc (x - y) * (x + y) = x^2 - y^2 : by ring
     ... = y^2 - y^2                   : by rw h
     ... = 0                           : by ring,
  have h2 : x - y = 0 ∨ x + y = 0,
    by apply eq_zero_or_eq_zero_of_mul_eq_zero h1,
  cases h2 with h2a h2b,
    { left,
      exact sub_eq_zero.mp h2a },
    { right,
      exact eq_neg_of_add_eq_zero h2b },
end

-- 2ª demostración
example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
have h1 : (x - y) * (x + y) = 0, from
  calc (x - y) * (x + y) = x^2 - y^2 : by ring
   ... = y^2 - y^2                   : by rw h
   ... = 0                           : by ring,
have h2 : x - y = 0 ∨ x + y = 0,
  from eq_zero_or_eq_zero_of_mul_eq_zero h1,
or.elim h2
  ( assume h2a : x - y = 0,
    have h3 : x = y,
      from sub_eq_zero.mp h2a,
    show x = y ∨ x = -y,
      from or.inl h3)
  ( assume h2b : x + y = 0,
    have h4 : x = -y,
      from eq_neg_of_add_eq_zero h2b,
    show x = y ∨ x = -y,
      from or.inr h4)

-- 3ª demostración
example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
-- by library_search
eq_or_eq_neg_of_pow_two_eq_pow_two x y h
