-- Igualdad a partir de acotaciones del valor absoluto de la diferencia
-- ====================================================================

import data.real.basic

variables (x y : ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la notación |x| para el valor
-- absoluto de x.
-- ----------------------------------------------------

notation `|`x`|` := abs x


lemma ig_de_abs_sub_me_todos : -- eq_of_abs_sub_le_all :
  (∀ ε > 0, |x - y| ≤ ε) → x = y :=
begin
  intro h,
  apply eq_of_abs_sub_nonpos,
  by_contradiction H,
  push_neg at H,
  specialize h ( |x-y|/2) (by linarith),
  linarith,
end
