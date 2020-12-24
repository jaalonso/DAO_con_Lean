-- Propiedad transitiva de la divisibilidad
-- ========================================

import tactic

variables (a b c : ℤ)

-- ----------------------------------------------------
-- Ejercicio. Denostrar que si a divide a b y b divide
-- a c, entonces a divide a c.
-- ----------------------------------------------------


-- 1ª demostración
example
  (h₁ : a ∣ b)
  (h₂ : b ∣ c)
  : a ∣ c :=
begin
  cases h₁ with k hk,
  cases h₂ with l hl,
  use k*l,
  calc c = b * l       : hl
     ... = (a * k) * l : by rw hk
     ... = a * (k * l) : mul_assoc a k l,
end

-- 2ª demostración
example
  (h₁ : a ∣ b)
  (h₂ : b ∣ c)
  : a ∣ c :=
begin
  cases h₁ with k hk,
  cases h₂ with l hl,
  use k*l,
  rw [hl, hk, mul_assoc],
end

-- 3ª demostración
example
  (h₁ : a ∣ b)
  (h₂ : b ∣ c)
  : a ∣ c :=
begin
  cases h₁ with k hk,
  cases h₂ with l hl,
  use k*l,
  calc c = b * l       : hl
     ... = (a * k) * l : by rw hk
     ... = a * (k * l) : by ring,
end

-- 4ª demostración
example
  (h₁ : a ∣ b)
  (h₂ : b ∣ c)
  : a ∣ c :=
-- by library_search
dvd_trans h₁ h₂
