-- En los naturales, mcd(a,b) = a syss a divide a b
-- ================================================

-- Sean a y b son números naturales. Entonces
--    a ∣ b ↔ gcd a b = a

-- Lemas auxiliares:
-- + dvd_refl:      a ∣ a
-- + dvd_antisymm : a ∣ b → b ∣ a → a = b 
-- + dvd_gcd_iff :  c ∣ gcd a b ↔ c ∣ a ∧ c ∣ b
-- + gcd_dvd :      gcd a b ∣ a ∧ gcd a b ∣ b

import data.nat.gcd

open nat

variables (a b : ℕ)

-- 1ª demostración
-- ===============

example : a ∣ b ↔ gcd a b = a :=
begin
  have h1 : gcd a b ∣ a ∧ gcd a b ∣ b,
  { exact gcd_dvd a b, },
  split,
  { intro h2,
    apply dvd_antisymm h1.left,
    rw dvd_gcd_iff,
    exact ⟨dvd_refl a, h2⟩, },
  { intro h3,
    rw ← h3,
    exact h1.right, },
end

-- 2ª demostración
-- ===============

example : a ∣ b ↔ gcd a b = a :=
gcd_eq_left_iff_dvd
