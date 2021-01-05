-- Igualdad a partir de acotaciones del valor absoluto de la diferencia
-- ====================================================================

import data.real.basic

variables (x y : ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la notación |x| para el valor
-- absoluto de x.
-- ----------------------------------------------------

notation `|`x`|` := abs x

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar que si |x - y| ≤ ε, para todo
-- ε > 0, entonces x = y.
-- ----------------------------------------------------

-- Se usará el lema demostrado anteriormente
lemma cero_de_abs_mne_todos
  (h : ∀ ε > 0, |x| ≤ ε)
  : x = 0 :=
abs_eq_zero.mp
  (eq_of_le_of_forall_le_of_dense (abs_nonneg x) h)

-- 1ª demostración
example
  (h : ∀ ε > 0, |x - y| ≤ ε)
  : x = y :=
begin
  rw ← sub_eq_zero,
  exact cero_de_abs_mne_todos (x - y) h,
end

-- 2ª demostración
lemma ig_de_abs_sub_mne_todos
  (h : ∀ ε > 0, |x - y| ≤ ε)
  : x = y :=
sub_eq_zero.mp (cero_de_abs_mne_todos (x - y) h)
