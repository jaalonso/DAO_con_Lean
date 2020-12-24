-- Propiedad: Si divide a los sumandos divide a la suma
-- ====================================================

import tactic

variables (a b c : ℤ)

-- ----------------------------------------------------
-- Ejercicio. Demostrar que si a divide a b y a c,
-- entonces a divide a b+c.
-- ----------------------------------------------------

-- ?ª demostración
example
  (h1 : a ∣ b)
  (h2 : a ∣ c)
  : a ∣ b + c :=
begin
  cases h1 with k hk,
  rw hk,
  cases h2 with l hl,
  rw hl,
  use k+l,
  ring,
end

-- ?ª demostración
example
  (h1 : a ∣ b)
  (h2 : a ∣ c)
  : a ∣ b + c :=
begin
  rcases h1 with ⟨k, rfl⟩,
  rcases h2 with ⟨l, rfl⟩,
  use k+l,
  ring,
end
