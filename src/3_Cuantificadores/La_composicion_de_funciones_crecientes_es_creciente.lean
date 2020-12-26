-- La composición de funciones crecientes es creciente
-- ===================================================

import data.real.basic

variables (f g : ℝ → ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    creciente : (ℝ → ℝ) → Prop
-- tal que (creciente f) expresa que f es creciente.
-- ----------------------------------------------------

def creciente (f : ℝ → ℝ) : Prop :=
∀ {x₁ x₂}, x₁ ≤ x₂ → f x₁ ≤ f x₂

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar que la composición de
-- funciones crecientes es creciente.
-- ----------------------------------------------------

-- 1ª demostración
example
  (hf : creciente f)
  (hg : creciente g)
  : creciente (g ∘ f) :=
begin
  intros x₁ x₂ h,
  apply hg,
  apply hf,
  exact h,
end

-- 2ª demostración
example
  (hf : creciente f)
  (hg : creciente g)
  : creciente (g ∘ f) :=
begin
  intros x₁ x₂ h,
  apply hg,
  exact hf h,
end

-- 3ª demostración
example
  (hf : creciente f)
  (hg : creciente g)
  : creciente (g ∘ f) :=
begin
  intros x₁ x₂ h,
  exact hg (hf h),
end

-- 4ª demostración
example
  (hf : creciente f)
  (hg : creciente g)
  : creciente (g ∘ f) :=
λ x₁ x₂ h, hg (hf h)

-- 5ª demostración
example
  (hf : creciente f)
  (hg : creciente g)
  : creciente (g ∘ f) :=
begin
  intros x₁ x₂ h,
  specialize hf h,
  exact hg hf,
end

-- 6ª demostración
example
  (hf : creciente f)
  (hg : creciente g)
  : creciente (g ∘ f) :=
assume x₁ x₂,
assume h1 : x₁ ≤ x₂,
have h2 : f x₁ ≤ f x₂,
  from hf h1,
show (g ∘ f) x₁ ≤ (g ∘ f) x₂, from
  calc (g ∘ f) x₁
       = g (f x₁)   : rfl
   ... ≤ g (f x₂)   : hg h2
   ... ≤ (g ∘ f) x₂ : by refl

-- Nota. La función predefinida monotone es equivalente
-- a creciente. El lema es
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
-- by library_search
monotone.comp hg hf
