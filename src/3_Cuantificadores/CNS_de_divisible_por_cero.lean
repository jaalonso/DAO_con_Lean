-- CNS de divisible por cero
-- =========================

import tactic

variable (a : ℤ)

-- 1ª demostración
example : 0 ∣ a ↔ a = 0 :=
begin
  split,
  { intro h,
    cases h with k hk,
    rw hk,
    exact zero_mul k, },
  { intro h,
    rw h, },
end

-- 2ª demostración
example : 0 ∣ a ↔ a = 0 :=
begin
  split,
  { intro h,
    rcases h with ⟨k, rfl⟩,
    exact zero_mul k, },
  { intro h,
    rw h, },
end

-- 3ª demostración
example : 0 ∣ a ↔ a = 0 :=
begin
  split,
  { rintro ⟨k, rfl⟩,
    ring, },
  { rintro rfl,
    use 0,
    refl, },
end
