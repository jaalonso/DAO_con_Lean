-- Propiedad: ∀ x y : ℝ, x^2 = y^2 → x = y ∨ x = -y
-- ================================================

import data.real.basic

variables (x y : ℝ)

-- -----------------------------------------------------
-- Ejercicio. Demostrar si
--    x^2 = y^2
-- entonces
--    x = y ∨ x = -y
-- -----------------------------------------------------

-- 1ª demostración
example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
begin
  have h1 : (x - y) * (x + y) = 0,
    calc (x - y) * (x + y)
         = x^2 - y^2       : by ring
     ... = y^2 - y^2       : by rw h
     ... = 0               : by ring,
  have h2 : x - y = 0 ∨ x + y = 0,
    by exact mul_eq_zero.mp h1,
  cases h2 with h2a h2b,
    { left,
      exact sub_eq_zero.mp h2a, },
    { right,
      exact eq_neg_of_add_eq_zero h2b, },
end

-- 2ª demostración
example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
begin
  have h1 : (x - y) * (x + y) = 0,
    by linarith,
  have h2 : x - y = 0 ∨ x + y = 0,
    by finish,
  cases h2 with h2a h2b,
    { left,
      linarith, },
    { right,
      linarith, },
end

-- 3ª demostración
example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
have h1 : (x - y) * (x + y) = 0, from
  calc (x - y) * (x + y) = x^2 - y^2 : by ring
   ... = y^2 - y^2                   : by rw h
   ... = 0                           : by ring,
have h2 : x - y = 0 ∨ x + y = 0,
  from mul_eq_zero.mp h1,
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

-- 4ª demostración
example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
have h1 : (x - y) * (x + y) = 0, from
  by linarith,
have h2 : x - y = 0 ∨ x + y = 0,
  by finish,
or.elim h2
  ( assume h2a : x - y = 0,
    have h3 : x = y,
      by linarith,
    show x = y ∨ x = -y,
      from or.inl h3)
  ( assume h2b : x + y = 0,
    have h4 : x = -y,
      by linarith,
    show x = y ∨ x = -y,
      from or.inr h4)

-- 5ª demostración
example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
-- by library_search
eq_or_eq_neg_of_pow_two_eq_pow_two x y h

-- 6ª demostración
example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
begin
 rw ← add_eq_zero_iff_eq_neg,
 rw ← sub_eq_zero,
 rw or_comm,
 rw ← mul_eq_zero,
 rw ← pow_two_sub_pow_two x y,
 rw sub_eq_zero,
 assumption,
end

-- 7ª demostración
example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
by rwa [← add_eq_zero_iff_eq_neg,
        ← sub_eq_zero,
        or_comm,
        ← mul_eq_zero,
        ← pow_two_sub_pow_two x y,
        sub_eq_zero]
