-- Si |x| < ε, para todo ε > 0, entonces x = 0
-- ===========================================

import data.real.basic

variable (x : ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la notación |x| para el valor
-- absoluto de x.
-- ----------------------------------------------------

notation `|`x`|` := abs x

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar que si |x| < ε, para todo
-- ε > 0, entonces x = 0
-- ----------------------------------------------------

-- 1ª demostración
example
  (h : ∀ ε > 0, |x| < ε)
  : x = 0 :=
begin
  rw ← abs_eq_zero,
  apply eq_of_le_of_forall_le_of_dense,
  { exact abs_nonneg x, },
  { intros ε hε,
    apply le_of_lt,
    exact h ε hε, },
end

-- 2ª demostración
example
  (h : ∀ ε > 0, |x| < ε)
  : x = 0 :=
begin
  rw ← abs_eq_zero,
  apply eq_of_le_of_forall_le_of_dense,
  { exact abs_nonneg x, },
  { intros ε hε,
    exact le_of_lt (h ε hε), },
end

-- 3ª demostración
example
  (h : ∀ ε > 0, |x| < ε)
  : x = 0 :=
begin
  rw ← abs_eq_zero,
  apply eq_of_le_of_forall_le_of_dense,
  { exact abs_nonneg x, },
  { exact λ ε hε, le_of_lt (h ε hε), },
end

-- 4ª demostración
example
  (h : ∀ ε > 0, |x| < ε)
  : x = 0 :=
begin
  rw ← abs_eq_zero,
  apply eq_of_le_of_forall_le_of_dense
        (abs_nonneg x)
        (λ ε hε, le_of_lt (h ε hε)),
end

-- 5ª demostración
example
  (h : ∀ ε > 0, |x| < ε)
  : x = 0 :=
abs_eq_zero.mp
  (eq_of_le_of_forall_le_of_dense
    (abs_nonneg x)
    (λ ε hε, le_of_lt (h ε hε)))

-- 6ª demostración
example
  (h : ∀ ε > 0, |x| < ε)
  : x = 0 :=
have h1 : 0 ≤ |x|,
  from abs_nonneg x,
have h2 : ∀ ε, ε > 0 → |x| ≤ ε,
  { assume ε,
    assume hε : ε > 0,
    have h2a : |x| < ε,
      from h ε hε,
    show |x| ≤ ε,
      from le_of_lt h2a },
have h3 : |x| = 0,
  from eq_of_le_of_forall_le_of_dense h1 h2,
show x = 0,
  from abs_eq_zero.mp h3

-- 7ª demostración
example
  (h : ∀ ε > 0, |x| < ε)
  : x = 0 :=
have h1 : 0 ≤ |x|,
  from abs_nonneg x,
have h2 : ∀ ε, ε > 0 → |x| ≤ ε,
  { assume ε,
    assume hε : ε > 0,
    have h2a : |x| < ε,
      from h ε hε,
    show |x| ≤ ε,
      from le_of_lt h2a },
have h3 : |x| = 0,
  from eq_of_le_of_forall_le_of_dense h1 h2,
abs_eq_zero.mp h3

-- 8ª demostración
example
  (h : ∀ ε > 0, |x| < ε)
  : x = 0 :=
have h1 : 0 ≤ |x|,
  from abs_nonneg x,
have h2 : ∀ ε, ε > 0 → |x| ≤ ε,
  { assume ε,
    assume hε : ε > 0,
    have h2a : |x| < ε,
      from h ε hε,
    show |x| ≤ ε,
      from le_of_lt h2a },
abs_eq_zero.mp (eq_of_le_of_forall_le_of_dense h1 h2)

-- 9ª demostración
example
  (h : ∀ ε > 0, |x| < ε)
  : x = 0 :=
have h1 : 0 ≤ |x|,
  from abs_nonneg x,
have h2 : ∀ ε, ε > 0 → |x| ≤ ε,
  { assume ε,
    assume hε : ε > 0,
    show |x| ≤ ε,
      from le_of_lt (h ε hε) },
abs_eq_zero.mp (eq_of_le_of_forall_le_of_dense h1 h2)

-- 10ª demostración
lemma cero_de_abs_mn_todos
  (h : ∀ ε > 0, |x| < ε)
  : x = 0 :=
abs_eq_zero.mp
  (eq_of_le_of_forall_le_of_dense
    (abs_nonneg x)
    (λ ε hε, le_of_lt (h ε hε)))
