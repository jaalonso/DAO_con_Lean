-- La relación menor es irreflexiva en los reales
-- ==============================================

import data.real.basic
import tactic

variable {x : ℝ}

-- ----------------------------------------------------
-- Ejercicio. Demostrar que la relación menor es
-- irreflexiva en los reales.
-- ----------------------------------------------------

-- 1ª demostración
example : ¬ x < x :=
begin
  intro h1,
  rw lt_iff_le_and_ne at h1,
  cases h1 with h2 h3,
  -- clear h2,
  -- change x = x → false at h3,
  apply h3,
  refl,
end

-- 2ª demostración
example : ¬ x < x :=
begin
  intro h1,
  rw lt_iff_le_and_ne at h1,
  cases h1 with h2 h3,
  apply h3,
  refl,
end

-- 3ª demostración
example : ¬ x < x :=
begin
  intro h1,
  cases (lt_iff_le_and_ne.mp h1) with h2 h3,
  apply h3,
  refl,
end

-- 4ª demostración
example : ¬ x < x :=
begin
  intro h1,
  apply (lt_iff_le_and_ne.mp h1).2,
  refl,
end

-- 5ª demostración
example : ¬ x < x :=
begin
  intro h1,
  exact absurd rfl (lt_iff_le_and_ne.mp h1).2,
end

-- 6ª demostración
example : ¬ x < x :=
λ h, absurd rfl (lt_iff_le_and_ne.mp h).2

-- 7ª demostración
example : ¬ x < x :=
assume h1 : x < x,
have h2 : x ≤ x ∧ x ≠ x,
  from lt_iff_le_and_ne.mp h1,
have h3 : x ≠ x,
  from and.right h2,
have h4 : x = x,
  from rfl,
show false,
  from absurd h4 h3

-- 8ª demostración
example : ¬ x < x :=
assume h1 : x < x,
have h2 : x ≤ x ∧ x ≠ x,
  from lt_iff_le_and_ne.mp h1,
absurd rfl (and.right h2)

-- 9ª demostración
example : ¬ x < x :=
assume h1 : x < x,
absurd rfl (and.right (lt_iff_le_and_ne.mp h1))

-- 10ª demostración
example : ¬ x < x :=
assume h1 : x < x,
absurd rfl (lt_iff_le_and_ne.mp h1).2

-- 11ª demostración
example : ¬ x < x :=
λ h, absurd rfl (lt_iff_le_and_ne.mp h).2

-- 12ª demostración
example : ¬ x < x :=
-- by library_search
irrefl x

-- 12ª demostración
example : ¬ x < x :=
-- by hint
by simp

-- 13ª demostración
example : ¬ x < x :=
by finish

-- 14ª demostración
example : ¬ x < x :=
by norm_num

-- 15ª demostración
example : ¬ x < x :=
by linarith

-- 16ª demostración
example : ¬ x < x :=
by nlinarith
