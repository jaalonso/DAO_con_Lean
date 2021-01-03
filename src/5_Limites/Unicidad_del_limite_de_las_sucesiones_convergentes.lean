-- Unicidad del límite de las sucesiones convergentes
-- ==================================================

import data.real.basic

variables (u : ℕ → ℝ)
variables (a b : ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la notación |x| para el valor
-- absoluto de x.
-- ----------------------------------------------------

notation `|`x`|` := abs x

-- ----------------------------------------------------
-- Ejercicio 2. Definir la función
--    limite : (ℕ → ℝ) → ℝ → Prop
-- tal que (limite u c) expresa que c es el límite de
-- la sucesión u.
-- ----------------------------------------------------

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε



example : limite u a → limite u b → a = b :=
begin
  -- sorry
  intros ha hb,
  apply eq_of_abs_sub_le_all,
  intros ε ε_pos,
  cases ha (ε/2) (by linarith) with N hN,
  cases hb (ε/2) (by linarith) with N' hN',
  calc |a - b| = |(a-u (max N N')) + (u (max N N') -b)| : by ring
  ... ≤ |a - u (max N N')| + |u (max N N') - b| : by apply abs_add
  ... =  |u (max N N') - a| + |u (max N N') - b| : by rw abs_sub
  ... ≤ ε : by linarith [hN (max N N') (le_max_left _ _), hN' (max N N') (le_max_right _ _)]
  -- sorry
end
