-- Una función creciente e involutiva es la identidad
-- ==================================================

import data.real.basic

variables (x y : ℝ)
variables (f g : ℝ → ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    creciente : (ℝ → ℝ) → Prop
-- tal que (creciente f) espresa que f es creciente.
-- ----------------------------------------------------

def creciente (f : ℝ → ℝ) : Prop :=
∀ {x₁ x₂}, x₁ ≤ x₂ → f x₁ ≤ f x₂

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar que si f es creciente y
--    ∀ x, f (f x) = x
-- entonces es la identidad.
-- ----------------------------------------------------

-- 1ª demostración
example
  (h : creciente f)
  (h' : ∀ x, f (f x) = x)
  : ∀ x, f x = x :=
begin
  intro x,
  cases (le_total (f x) x) with h1 h2,
  { apply antisymm h1,
    have h3 : f (f x) ≤ f x,
      { apply h,
        exact h1, },
    rwa h' x at h3, },
  { apply antisymm _ h2,
    have h4 : f x ≤ f (f x),
      { apply h,
        exact h2, },
    rwa h' x at h4, },
end

-- 2ª demostración
example
  (h : creciente f)
  (h' : ∀ x, f (f x) = x)
  : ∀ x, f x = x :=
begin
  intro x,
  cases (le_total (f x) x) with h1 h2,
  { apply antisymm h1,
    calc x
         = f (f x) : by exact (h' x).symm
     ... ≤ f x     : by exact h h1 },
  { apply antisymm _ h2,
    calc f x
         ≤ f (f x) : by exact h h2
     ... = x       : by exact h' x },
end
