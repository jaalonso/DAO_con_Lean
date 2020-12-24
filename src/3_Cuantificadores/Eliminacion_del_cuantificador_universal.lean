-- Eliminación del cuantificador universal
-- =======================================

import tactic

variable (P : ℕ → Prop)

-- ----------------------------------------------------
-- Ejercicio 1. Demostrar que si todos los números
-- naturales tienen la propiedad P, entonces el cero
-- tiene la propiedad P.
-- ----------------------------------------------------

-- 1ª demostración
example
  (h : ∀ n, P n)
  : P 0 :=
-- by library_search
by exact h 0

-- 2ª demostración
example
  (h : ∀ n, P n)
  : P 0 :=
h 0

-- 3ª demostración
example
  (h : ∀ n, P n)
  : P 0 :=
begin
  specialize h 0,
  exact h,
end

-- 4ª demostración
example
  (h : ∀ n, P n)
  : P 0 :=
-- by hint
by tauto

-- 5ª demostración
example
  (h : ∀ n, P n)
  : P 0 :=
by finish
