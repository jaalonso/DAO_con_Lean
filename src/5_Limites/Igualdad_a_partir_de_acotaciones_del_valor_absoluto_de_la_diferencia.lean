-- Igualdad a partir de acotaciones del valor absoluto de la diferencia
-- ====================================================================

import data.real.basic

variables (x y : ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la notación |x| para el valor
-- absoluto de x.
-- ----------------------------------------------------

notation `|`x`|` := abs x

-- ?ª demostración
example :
  (∀ ε > 0, |x - y| ≤ ε) → x = y :=
begin
  intro h,
  apply eq_of_abs_sub_nonpos,
  by_contradiction h1,
  push_neg at h1,
  have h2 : |x - y|/2 > 0,
    { exact half_pos h1, },
  specialize h (|x - y|/2) h2,
  have h3 : |x - y| > |x - y|/2 ,
    { exact half_lt_self h1, },
  contrapose h3,
  exact not_lt_of_le h,
end

-- ?ª demostración
example :
  (∀ ε > 0, |x - y| ≤ ε) → x = y :=
assume h1 : ∀ ε > 0, |x - y| ≤ ε,
suffices |x - y| ≤ 0,
  from eq_of_abs_sub_nonpos,
sorry

lemma ig_de_abs_sub_mne_todos :
  (∀ ε > 0, |x - y| ≤ ε) → x = y :=
begin
  intro h,
  apply eq_of_abs_sub_nonpos,
  by_contradiction H,
  push_neg at H,
  specialize h (|x-y|/2) (by linarith),
  linarith,
end
