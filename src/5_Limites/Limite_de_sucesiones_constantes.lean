-- Límite de sucesiones constantes
-- ===============================

import data.real.basic

variable (u : ℕ → ℝ)
variable (c : ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la notación |x| para el valor
-- absoluto de x.
-- ----------------------------------------------------

notation `|`x`|` := abs x

-- ----------------------------------------------------
-- Ejercicio 2. Definir la función
--    limite : (ℕ → ℝ) → ℝ → Prop
-- tal que (limite u c) expresa que c es el límite de
-- la sucesión u.
-- ----------------------------------------------------

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε

-- ----------------------------------------------------
-- Ejercicio 3. Demostrar que si u es la sucesión
-- constante c, entonces el límite de u es c.
-- ----------------------------------------------------

-- 1ª demostración
example :
  (∀ n, u n = c) → limite u c :=
begin
  intro hu,
  unfold limite,
  intro ε,
  intro hε,
  use 0,
  intro n',
  intro hn',
  specialize hu n',
  rw hu,
  norm_num,
  linarith,
end

-- 2ª demostración
example :
  (∀ n, u n = c) → limite u c :=
begin
  intros hu ε hε,
  use 0,
  intros n' hn',
  rw hu n',
  norm_num,
  linarith,
end

-- 3ª demostración
example :
  (∀ n, u n = c) → limite u c :=
begin
  intros hu ε hε,
  use 0,
  intros n hn,
  rw hu,
  norm_num,
  linarith,
end

-- 4ª demostración
example :
  (∀ n, u n = c) → limite u c :=
begin
  intros hu ε hε,
  use 0,
  intros n' hn',
  calc |u n' - c|
       = |c - c|  : by rw hu
   ... = 0        : by norm_num
   ... ≤ ε        : by linarith,
end

-- 5ª demostración
example :
  (∀ n, u n = c) → limite u c :=
assume hu : ∀ n, u n = c,
assume ε,
assume hε : ε > 0,
exists.intro 0
  ( assume n',
    assume hn' : n' ≥ 0,
    show |u n' - c| ≤ ε, from
      calc |u n' - c|
           = |c - c|  : by rw hu
       ... = 0        : by norm_num
       ... ≤ ε        : by linarith)
