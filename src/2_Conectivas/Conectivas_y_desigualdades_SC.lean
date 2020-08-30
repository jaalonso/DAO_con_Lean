-- Conectivas y desigualdades
-- ==========================

-- En esta relación se formulan algunas de las 
-- anteriores propiedades de las desigualdades de los 
-- números reales usando conectivas.

import data.real.basic

variables (a b c : ℝ)

-- Ej1. Demostrar que
--    0 ≤ a → b ≤ a + b

-- 1ª demostración
-- ===============

example : 0 ≤ a → b ≤ a + b :=
begin
  intro ha,
  exact le_add_of_nonneg_left ha,
end

-- 2ª demostración
-- ===============

example : 0 ≤ a → b ≤ a + b :=
le_add_of_nonneg_left

-- 3ª demostración
-- ===============

example : 0 ≤ a → b ≤ a + b :=
by finish

-- Ej2. Demostrar que
--    0 ≤ b → a ≤ a + b

-- 1ª demostración
-- ===============

example: 0 ≤ b → a ≤ a + b :=
begin
  intro hb,
  exact le_add_of_nonneg_right hb,
end

-- 2ª demostración
-- ===============

example: 0 ≤ b → a ≤ a + b :=
le_add_of_nonneg_right

-- 3ª demostración
-- ===============

example: 0 ≤ b → a ≤ a + b :=
by finish

-- Ej3. Demostrar que
--    (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b

-- 1ª demostración
-- ===============

example : (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b :=
begin
  intros hab,
  cases hab with ha hb,
  exact add_nonneg ha hb,
end

-- 2ª demostración
-- ===============

example : (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b :=
begin
  rintros ⟨ha, hb⟩,
  exact add_nonneg ha hb,
end

-- 3ª demostración
-- ===============

example : (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b :=
λ ⟨ha, hb⟩, add_nonneg ha hb

-- Ej4. Demostrar que
--    0 ≤ a → (0 ≤ b → 0 ≤ a + b)

-- 1ª demostración
-- ===============

example : 0 ≤ a → (0 ≤ b → 0 ≤ a + b) := 
begin
  intro ha,
  intro hb,
  exact add_nonneg ha hb,
end

-- 2ª demostración
-- ===============

example : 0 ≤ a → (0 ≤ b → 0 ≤ a + b) := 
begin
  intros ha hb,
  exact add_nonneg ha hb,
end

-- 3ª demostración
-- ===============

example : 0 ≤ a → (0 ≤ b → 0 ≤ a + b) := 
λ ha hb, add_nonneg ha hb

-- 4ª demostración
-- ===============

example : 0 ≤ a → (0 ≤ b → 0 ≤ a + b) := 
add_nonneg

-- 5ª demostración
-- ===============

example : 0 ≤ a → (0 ≤ b → 0 ≤ a + b) := 
by intros ; linarith 

-- Ej5. Demostrar que si
--   (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b
-- entonces 
--   0 ≤ a → (0 ≤ b → 0 ≤ a + b)

-- 1ª demostración
-- ===============

example 
  (H : (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b) 
  : 0 ≤ a → (0 ≤ b → 0 ≤ a + b) :=
begin
  intro ha,
  intro hb,
  apply H,
  split,
  { exact ha, },
  { exact hb, },
end

-- 2ª demostración
-- ===============

example 
  (H : (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b) 
  : 0 ≤ a → (0 ≤ b → 0 ≤ a + b) :=
begin
  intros ha hb,
  apply H,
  split,
  { exact ha, },
  { exact hb, },
end

-- 3ª demostración
-- ===============

example 
  (H : (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b) 
  : 0 ≤ a → (0 ≤ b → 0 ≤ a + b) :=
begin
  intros ha hb,
  exact H ⟨ha, hb⟩,
end

-- 4ª demostración
-- ===============

example 
  (H : (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b) 
  : 0 ≤ a → (0 ≤ b → 0 ≤ a + b) :=
λ ha hb, H ⟨ha, hb⟩

-- 5ª demostración
-- ===============

example 
  (H : (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b) 
  : 0 ≤ a → (0 ≤ b → 0 ≤ a + b) :=
by tauto

-- 6ª demostración
-- ===============

example 
  (H : (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b) 
  : 0 ≤ a → (0 ≤ b → 0 ≤ a + b) :=
by finish

