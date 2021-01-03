-- Si |x| ≤ ε, para todo ε > 0, entonces x = 0
-- ===========================================

import data.real.basic

variable (x : ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la notación |x| para el valor
-- absoluto de x.
-- ----------------------------------------------------

notation `|`x`|` := abs x

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar que si |x| ≤ ε, para todo
-- ε > 0, entonces x = 0
-- ----------------------------------------------------

-- 1ª demostración
example
  (h : ∀ ε > 0, |x| ≤ ε)
  : x = 0 :=
begin
  rw ← abs_eq_zero,
  apply eq_of_le_of_forall_le_of_dense,
  { exact abs_nonneg x, },
  { intros ε hε,
    exact h ε hε, },
end

-- 2ª demostración
example
  (h : ∀ ε > 0, |x| ≤ ε)
  : x = 0 :=
begin
  rw ← abs_eq_zero,
  apply eq_of_le_of_forall_le_of_dense,
  { exact abs_nonneg x, },
  { intros ε hε,
    exact h ε hε, },
end

-- 3ª demostración
example
  (h : ∀ ε > 0, |x| ≤ ε)
  : x = 0 :=
begin
  rw ← abs_eq_zero,
  apply eq_of_le_of_forall_le_of_dense,
  { exact abs_nonneg x, },
  { exact λ ε hε, h ε hε, },
end

-- 4ª demostración
example
  (h : ∀ ε > 0, |x| ≤ ε)
  : x = 0 :=
begin
  rw ← abs_eq_zero,
  apply eq_of_le_of_forall_le_of_dense
        (abs_nonneg x)
        h,
end

-- 5ª demostración
example
  (h : ∀ ε > 0, |x| ≤ ε)
  : x = 0 :=
abs_eq_zero.mp
  (eq_of_le_of_forall_le_of_dense (abs_nonneg x) h)

-- 6ª demostración
example
  (h : ∀ ε > 0, |x| ≤ ε)
  : x = 0 :=
have h1 : 0 ≤ |x|,
  from abs_nonneg x,
have h2 : |x| = 0,
  from eq_of_le_of_forall_le_of_dense h1 h,
show x = 0,
  from abs_eq_zero.mp h2

-- 7ª demostración
example
  (h : ∀ ε > 0, |x| ≤ ε)
  : x = 0 :=
have h1 : 0 ≤ |x|,
  from abs_nonneg x,
have h2 : |x| = 0,
  from eq_of_le_of_forall_le_of_dense h1 h,
abs_eq_zero.mp h2

-- 8ª demostración
example
  (h : ∀ ε > 0, |x| ≤ ε)
  : x = 0 :=
have h1 : 0 ≤ |x|,
  from abs_nonneg x,
abs_eq_zero.mp (eq_of_le_of_forall_le_of_dense h1 h)

-- 9ª demostración
lemma cero_de_abs_mn_todos
  (h : ∀ ε > 0, |x| ≤ ε)
  : x = 0 :=
abs_eq_zero.mp
  (eq_of_le_of_forall_le_of_dense (abs_nonneg x) h)
