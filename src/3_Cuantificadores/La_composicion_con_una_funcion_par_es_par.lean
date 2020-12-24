-- La composición con una función par es par
-- =========================================

import data.real.basic

variables (f g : ℝ → ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    par : (ℝ → ℝ) → Prop
-- tal que (par f) expresa que f es par.
-- ----------------------------------------------------

def par (f : ℝ → ℝ) : Prop :=
∀ x, f (-x) = f x

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar que si f es par, entonces
-- (g ∘ f) también lo es.
-- ----------------------------------------------------

-- 1ª demostración
example
 : par f → par (g ∘ f) :=
begin
  intros hf x,
  simp,
  rw hf,
end

-- 2ª demostración
example
 : par f → par (g ∘ f) :=
begin
  intros hf x,
  calc (g ∘ f) (-x)
       = g (f (-x)) : rfl
   ... = g (f (x))  : by rw hf
   ... = (g ∘ f) x  : rfl
end

-- 3ª demostración
example
 : par f → par (g ∘ f) :=
begin
  intros hf x,
  calc (g ∘ f) (-x)
       = g (f (-x)) : rfl
   ... = g (f (x))  : by rw hf
end
