-- La función duplicadora no es par
-- ================================

import data.real.basic

variable (f : ℝ → ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    par : (ℝ → ℝ) → Prop
-- tal que (par f) expresa que f es par.
-- ----------------------------------------------------

def par : (ℝ → ℝ) → Prop
| f := ∀ x, f (-x) = f x

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar que la función que a cada x
-- le asigna 2*x no es par.
-- ----------------------------------------------------

example :
  ¬par (λ x, 2*x) :=
begin
  unfold par,
  push_neg,
  use 42,
  linarith,
end
