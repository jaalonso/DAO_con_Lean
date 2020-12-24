-- f es creciente syss ∀ x y, x < y → f x ≤ f y
-- ============================================

import data.real.basic

variable (f : ℝ → ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    creciente : (ℝ → ℝ) → Prop
-- tal que (creciente f) espresa que f es creciente.
-- ----------------------------------------------------

def creciente (f : ℝ → ℝ) : Prop :=
∀ {x₁ x₂}, x₁ ≤ x₂ → f x₁ ≤ f x₂

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar que f es creciente syss
-- ∀ x y, x < y → f x ≤ f y
-- ----------------------------------------------------

-- 1ª demostración
example :
  creciente f ↔ ∀ x y, x < y → f x ≤ f y :=
begin
  split,
  { intros hf x y hxy,
    apply hf,
    exact le_of_lt hxy, },
  { intros h x y hxy,
    have h1: x = y ∨ x < y,
      apply eq_or_lt_of_le hxy,
    cases h1 with h2 h3,
    { rw h2, },
    { apply h,
      exact h3, }},
end

-- 2ª demostración
example :
  creciente f ↔ ∀ x y, x < y → f x ≤ f y :=
begin
  split,
  { intros hf x y hxy,
    apply hf,
    linarith, },
  { intros h x y hxy,
    cases (eq_or_lt_of_le hxy) with h2 h3,
    { rw h2, },
    { exact h x y h3, }},
end
