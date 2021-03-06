-- Propiedad: Si divide a los sumandos divide a la suma (con condicionales)
-- ========================================================================

import tactic

variables (a b c : ℤ)

-- ----------------------------------------------------
-- Ejercicio. Demostrar que
--    a ∣ b → a ∣ c → a ∣ b+c
-- ----------------------------------------------------

#print notation (∣)

-- 1ª demostración
example :
  a ∣ b → a ∣ c → a ∣ b+c :=
begin
  intros hab hac,
  -- unfold has_dvd.dvd at hab,
  cases hab with k hk,
  rw hk,
  cases hac with l hl,
  rw hl,
  use k+l,
  ring,
end

-- 2ª demostración
example :
  a ∣ b → a ∣ c → a ∣ b+c :=
begin
  intros hab hac,
  -- unfold has_dvd.dvd at hab,
  rcases hab with ⟨k, rfl⟩,
  rcases hac with ⟨l, rfl⟩,
  use k+l,
  ring,
end

-- 3ª demostración
example :
  a ∣ b → a ∣ c → a ∣ b+c :=
begin
  rintros ⟨k, rfl⟩ ⟨l, rfl⟩,
  use k+l,
  ring,
end
