-- La composición de una función creciente y una decreciente es decreciente
-- ========================================================================

import data.real.basic

variables (f g : ℝ → ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    creciente : (ℝ → ℝ) → Prop
-- tal que (creciente f) espresa que f es creciente.
-- ----------------------------------------------------

def creciente (f : ℝ → ℝ) : Prop :=
∀ {x₁ x₂}, x₁ ≤ x₂ → f x₁ ≤ f x₂

-- ----------------------------------------------------
-- Ejercicio 2. Definir la función
--    decreciente : (ℝ → ℝ) → Prop
-- tal que (decreciente f) espresa que f es decreciente.
-- ----------------------------------------------------

def decreciente (f : ℝ → ℝ) : Prop :=
∀ {x₁ x₂}, x₁ ≤ x₂ → f x₁ ≥ f x₂

-- ----------------------------------------------------
-- Ejercicio 3. Demostrar que si f es creciente y g es
-- decreciente, entonces (g ∘ f) es decreciente.
-- ----------------------------------------------------

-- 1ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
begin
  intros x₁ x₂ h,
  apply hg,
  apply hf,
  exact h,
end

-- 2ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
assume x₁ x₂,
assume h : x₁ ≤ x₂,
have h1 : f x₁ ≤ f x₂,
  from hf h,
show (g ∘ f) x₁ ≥ (g ∘ f) x₂,
  from hg h1

-- 3ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
assume x₁ x₂,
assume h : x₁ ≤ x₂,
show (g ∘ f) x₁ ≥ (g ∘ f) x₂,
  from hg (hf h)

-- 4ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
λ x₁ x₂ h, hg (hf h)
