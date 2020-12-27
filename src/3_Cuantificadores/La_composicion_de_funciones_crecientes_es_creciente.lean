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
  unfold creciente at *,
  intros x y h,
  unfold function.comp,
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
  intros x y h,
  apply hg,
  apply hf,
  exact h,
end

-- 3ª demostración
example
  (hf : creciente f)
  (hg : creciente g)
  : creciente (g ∘ f) :=
begin
  intros x xy h,
  apply hg,
  exact hf h,
end

-- 4ª demostración
example
  (hf : creciente f)
  (hg : creciente g)
  : creciente (g ∘ f) :=
begin
  intros x y h,
  exact hg (hf h),
end

-- 4ª demostración
example
  (hf : creciente f)
  (hg : creciente g)
  : creciente (g ∘ f) :=
λ x y h, hg (hf h)

-- 5ª demostración
example
  (hf : creciente f)
  (hg : creciente g)
  : creciente (g ∘ f) :=
begin
  intros x y h,
  specialize hf h,
  exact hg hf,
end

-- 6ª demostración
example
  (hf : creciente f)
  (hg : creciente g)
  : creciente (g ∘ f) :=
assume x y,
assume h1 : x ≤ y,
have h2 : f x ≤ f y,
  from hf h1,
show (g ∘ f) x ≤ (g ∘ f) y, from
  calc (g ∘ f) x
       = g (f x)   : rfl
   ... ≤ g (f y)   : hg h2
   ... = (g ∘ f) y : by refl

-- 7ª demostración
example
  (hf : creciente f)
  (hg : creciente g)
  : creciente (g ∘ f) :=
-- by hint
by tauto

-- Nota. La función predefinida monotone es equivalente
-- a creciente. El lema es
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
-- by library_search
monotone.comp hg hf
