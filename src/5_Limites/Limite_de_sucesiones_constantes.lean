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
  limite (λ n, c) c :=
begin
  -- unfold limite,
  intros ε hε,
  use 0,
  intros n hn,
  -- dsimp,
  norm_num,
  linarith,
end

-- 2ª demostración
example :
  limite (λ n, c) c :=
begin
  intros ε hε,
  use 0,
  intros n hn,
  norm_num,
  linarith,
end

-- 3ª demostración
example :
  limite (λ n, c) c :=
begin
  intros ε hε,
  use 0,
  intros n hn,
  calc |(λ n, c) n - c|
       = |c - c|  : rfl
   ... = 0        : by norm_num
   ... ≤ ε        : by linarith,
end

-- 4ª demostración
example :
  limite (λ n, c) c :=
assume ε,
assume hε : ε > 0,
exists.intro 0
  ( assume n,
    assume hn : n ≥ 0,
    show |(λ n, c) n - c| ≤ ε, from
      calc |(λ n, c) n - c|
           = |c - c|  : rfl
       ... = 0        : by norm_num
       ... ≤ ε        : by linarith)
