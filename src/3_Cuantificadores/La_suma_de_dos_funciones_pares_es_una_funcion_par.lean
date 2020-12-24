-- La suma de dos funciones pares es una función par
-- =================================================

import data.real.basic

variables (x y : ℝ)
variables (f g : ℝ → ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    par : (ℝ → ℝ) → Prop
-- tal que (par f) expresa que f es par.
-- ----------------------------------------------------

def par (f : ℝ → ℝ) : Prop :=
∀ x, f (-x) = f x

-- ----------------------------------------------------
-- Ejercicio 2. Definir la función
--    suma_funciones : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ)
-- tal que (suma_funciones f g) es la suma de las
-- funciones f y g.
-- ----------------------------------------------------

@[simp]
def suma_funciones (f g: ℝ → ℝ) : ℝ → ℝ :=
λ x, f x + g x

-- ----------------------------------------------------
-- Ejercicio 3. Definir la notación (f + g) para
-- representar (suma_funciones f g)
-- ----------------------------------------------------

notation f + g := suma_funciones f g

-- ----------------------------------------------------
-- Ejercicio 4. Demostrar que la suma de funciones
-- pares es par.
-- ----------------------------------------------------

-- 1ª demostración
example :
  par f → par g →  par (f + g) :=
begin
  intro hf,
  unfold par at hf,
  intro hg,
  unfold par at hg,
  unfold par,
  intro x,
  unfold suma_funciones,
  rw hf,
  rw hg,
end

-- 2ª demostración
example :
  par f → par g →  par (f + g) :=
begin
  intros hf hg x,
  simp [suma_funciones],
  rw [hf, hg],
end

-- 3ª demostración
example :
  par f → par g →  par (f + g) :=
begin
  intros hf hg x,
  unfold suma_funciones,
  rw [hf, hg],
end

-- 4ª demostración
example :
  par f → par g →  par (f + g) :=
begin
  intros hf hg x,
  calc (f + g) (-x)
       = f (-x) + g (-x) : rfl
   ... = f x + g (-x)    : by rw hf
   ... = f x + g x       : by rw hg
   ... = (f + g) x       : rfl
end

-- 5ª demostración
example :
  par f → par g →  par (f + g) :=
begin
  intros hf hg x,
  calc (f + g) (-x)
       = f (-x) + g (-x) : rfl
   ... = f x + g x       : by rw [hf, hg]
end
