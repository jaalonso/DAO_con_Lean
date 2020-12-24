-- La composición de funciones impares es impar
-- ============================================

import data.real.basic

variables (f g : ℝ → ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    impar : (ℝ → ℝ) → Prop
-- tal que (impar f) expresa que f es impar.
-- ----------------------------------------------------

def impar (f : ℝ → ℝ) : Prop :=
∀ x, f (-x) = -f x

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar que la composición de
-- funciones impares es impar.
-- ----------------------------------------------------

-- 1ª demostración
example :
  impar f → impar g →  impar (g ∘ f) :=
begin
  intros hf hg x,
  simp,
  rw hf,
  rw hg,
end

-- 2ª demostración
example :
  impar f → impar g →  impar (g ∘ f) :=
begin
  intros hf hg x,
  simp,
  rw [hf, hg],
end

-- 3ª demostración
example :
  impar f → impar g →  impar (g ∘ f) :=
begin
  intros hf hg x,
  calc (g ∘ f) (-x)
       = g (f (-x))  : rfl
   ... = g (- f x)   : by rw hf
   ... = -(g (f x))  : by rw hg
   ... = -(g ∘ f) x  : rfl,
end

-- 3ª demostración
example :
  impar f → impar g →  impar (g ∘ f) :=
begin
  intros hf hg x,
  calc (g ∘ f) (-x)
       = g (f (-x))  : rfl
   ... = -(g (f x))  : by rw [hf, hg]
end
