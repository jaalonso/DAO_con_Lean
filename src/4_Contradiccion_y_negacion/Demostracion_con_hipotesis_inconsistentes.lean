-- Demostración con hipótesis inconsistentes
-- =========================================

import data.int.parity
open int

variable (n : ℤ)

-- ----------------------------------------------------
-- Ejercicio. Demostrar que si un número es par y no es
-- par, entonces 0 = 1.
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : even n)
  (h2 : ¬ even n)
  : 0 = 1 :=
begin
  exfalso,
  exact h2 h1,
end

-- ?ª demostración
example
  (h1 : even n)
  (h2 : ¬ even n)
  : 0 = 1 :=
begin
  exact absurd h1 h2,
end

-- ?ª demostración
example
  (h1 : even n)
  (h2 : ¬ even n)
  : 0 = 1 :=
absurd h1 h2

-- ?ª demostración
example
  (h1 : even n)
  (h2 : ¬ even n)
  : 0 = 1 :=
-- by library_search
by exact false.rec (0 = 1) (h2 h1)

-- ?ª demostración
example
  (h1 : even n)
  (h2 : ¬ even n)
  : 0 = 1 :=
-- by hint
by tauto

-- ?ª demostración
example
  (h1 : even n)
  (h2 : ¬ even n)
  : 0 = 1 :=
by finish

-- ?ª demostración
example
  (h1 : even n)
  (h2 : ¬ even n)
  : 0 = 1 :=
by finish

-- ?ª demostración
example
  (h1 : even n)
  (h2 : ¬ even n)
  : 0 = 1 :=
by solve_by_elim
