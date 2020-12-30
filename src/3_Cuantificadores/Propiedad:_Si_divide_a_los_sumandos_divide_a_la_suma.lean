-- Propiedad: Si divide a los sumandos divide a la suma
-- ====================================================

import tactic
import algebra.divisibility

variables (a b c : ℤ)

-- ----------------------------------------------------
-- Ejercicio. Demostrar que si a divide a b y a c,
-- entonces a divide a b+c.
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : a ∣ b)
  (h2 : a ∣ c)
  : a ∣ b + c :=
begin
  -- unfold has_dvd.dvd at *,
  cases h1 with k hk,
  rw hk,
  cases h2 with l hl,
  rw hl,
  use k+l,
  rw left_distrib,
end

-- 2ª demostración
example
  (h1 : a ∣ b)
  (h2 : a ∣ c)
  : a ∣ b + c :=
begin
  cases h1 with k hk,
  cases h2 with l hl,
  use k+l,
  rw [hk, hl, left_distrib],
end

-- 3ª demostración
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

-- 4ª demostración
example
  (h1 : a ∣ b)
  (h2 : a ∣ c)
  : a ∣ b + c :=
dvd.elim h1
  ( assume k,
    assume hk : b = a * k,
    show a ∣ b + c, from
      dvd.elim h2
        ( assume l,
          assume hl : c = a * l,
          have h3 : a * (k + l) = b + c,
            by simp [hk, hl, left_distrib],
          show a ∣ b + c,
            from dvd.intro (k + l) h3))

-- 5ª demostración
example
  (h1 : a ∣ b)
  (h2 : a ∣ c)
  : a ∣ b + c :=
dvd.elim h1 (λ k hk,
  dvd.elim h2 (λ l hl,
     dvd.intro (k + l) (by simp [left_distrib, hk, hl])))

-- 6ª demostración
example
  (h1 : a ∣ b)
  (h2 : a ∣ c)
  : a ∣ b + c :=
-- by library_search
dvd_add h1 h2
