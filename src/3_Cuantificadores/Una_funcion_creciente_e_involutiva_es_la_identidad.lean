-- Una función creciente e involutiva es la identidad
-- ==================================================

import data.real.basic

variable (f : ℝ → ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    creciente : (ℝ → ℝ) → Prop
-- tal que (creciente f) expresa que f es creciente.
-- ----------------------------------------------------

def creciente (f : ℝ → ℝ) : Prop :=
∀ {x₁ x₂}, x₁ ≤ x₂ → f x₁ ≤ f x₂

-- ----------------------------------------------------
-- Ejercicio 2. Definir la función
--    involutiva : (ℝ → ℝ) → Prop
-- tal que (involutiva f) expresa que f es involutiva.
-- ----------------------------------------------------

def involutiva (f : ℝ → ℝ) : Prop :=
∀ {x}, f (f x) = x

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar que si f es creciente e
-- involutiva, entonces f es la identidad.
-- ----------------------------------------------------

-- 1ª demostración
example
  (hc : creciente f)
  (hi : involutiva f)
  : f = id :=
begin
  -- unfold creciente involutiva at *,
  funext,
  -- unfold id,
  cases (le_total (f x) x) with h1 h2,
  { apply antisymm h1,
    have h3 : f (f x) ≤ f x,
      { apply hc,
        exact h1, },
    rwa hi at h3, },
  { apply antisymm _ h2,
    have h4 : f x ≤ f (f x),
      { apply hc,
        exact h2, },
    rwa hi at h4, },
end

-- 2ª demostración
example
  (hc : creciente f)
  (hi : involutiva f)
  : f = id :=
begin
  funext,
  cases (le_total (f x) x) with h1 h2,
  { apply antisymm h1,
    calc x
         = f (f x) : hi.symm
     ... ≤ f x     : hc h1 },
  { apply antisymm _ h2,
    calc f x
         ≤ f (f x) : hc h2
     ... = x       : hi },
end
