-- La función identidad es menor o igual que la función de extracción
-- ==================================================================

import data.real.basic
open nat

variable {φ : ℕ → ℕ}

set_option pp.structure_projections false

-- ----------------------------------------------------
-- Ejercicio 1. Para extraer una subsucesión se aplica una
-- función de extracción que conserva el orden; por
-- ejemplo, la subsucesión
--    uₒ, u₂, u₄, u₆, ...
-- se ha obtenido con la función de extracción φ tal
-- que φ(n) = 2*n.
--
-- Definir la función
--    extraccion : (ℕ → ℕ) → Prop
-- tal que (extraccion φ) expresa que φ es una función
-- de extracción
-- ----------------------------------------------------

def extraccion : (ℕ → ℕ) → Prop
| φ := ∀ n m, n < m → φ n < φ m

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar que si φ es una función de
-- extracción, entonces
--    ∀ n, n ≤ φ n
-- ----------------------------------------------------

-- 1ª demostración
example :
  extraccion φ → ∀ n, n ≤ φ n :=
begin
  intros h n,
  induction n with m HI,
  { exact nat.zero_le (φ 0), },
  { apply nat.succ_le_of_lt,
    have h1 : m < succ m,
      from lt_add_one m,
    calc m ≤ φ m        : HI
       ... < φ (succ m) : h m (succ m) h1, },
end

-- 2ª demostración
example :
  extraccion φ → ∀ n, n ≤ φ n :=
begin
  intros h n,
  induction n with m HI,
  { exact nat.zero_le _ },
  { apply nat.succ_le_of_lt,
    calc m ≤ φ m        : HI
       ... < φ (succ m) : by linarith [h m (m+1) (by linarith)] },
end

-- 3ª demostración
example :
  extraccion φ → ∀ n, n ≤ φ n :=
begin
  intros h n,
  induction n with m HI,
  { linarith },
  { apply nat.succ_le_of_lt,
    linarith [h m (m+1) (by linarith)] },
end

-- 4ª demostración
example :
  extraccion φ → ∀ n, n ≤ φ n :=
begin
  intros h n,
  induction n with m HI,
  { linarith },
  { exact nat.succ_le_of_lt (by linarith [h m (m+1) (by linarith)]) },
end

-- 5ª demostración
example :
  extraccion φ → ∀ n, n ≤ φ n :=
assume h : extraccion φ,
assume n,
nat.rec_on n
  ( show 0 ≤ φ 0,
      from nat.zero_le (φ 0) )
  ( assume m,
    assume HI : m ≤ φ m,
    have h1 : m < succ m,
      from lt_add_one m,
    have h2 : m < φ (succ m), from
      calc m ≤ φ m        : HI
         ... < φ (succ m) : h m (succ m) h1,
    show succ m ≤ φ (succ m),
      from nat.succ_le_of_lt h2)
