-- Introducción del cuantificador existencial
-- ==========================================

import tactic

-- ----------------------------------------------------
-- Ejercicio. Demostrar que
--    ∃ k : ℕ, 8 = 2*k
-- ----------------------------------------------------

-- 1ª demostración
example : ∃ k : ℕ, 8 = 2*k :=
begin
  use 4,
  refl,
end

-- 2ª demostración
example : ∃ k : ℕ, 8 = 2*k :=
exists.intro 4
  ( show 8 = 2 * 4,
      from rfl)


-- 3ª demostración
example : ∃ k : ℕ, 8 = 2*k :=
exists.intro 4 rfl
