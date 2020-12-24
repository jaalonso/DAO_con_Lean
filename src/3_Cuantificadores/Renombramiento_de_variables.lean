-- Renombramiento de variables
-- ===========================

import tactic

variables (P Q : ℤ → Prop)

-- ----------------------------------------------------
-- Ejercicio ?. Demostrar que si
--    ∀ n, P n
--    ∀ n, P (n-1) → Q n
-- entonces
--    ∀ n, Q n
-- ----------------------------------------------------


-- 1ª demostración
example
  (hP : ∀ n, P n)
  (hPQ : ∀ n, P (n-1) → Q n)
  : ∀ n, Q n :=
begin
  intro n,
  apply hPQ,
  rename_var n m at hP,
  exact hP (n-1),
end

-- 2ª demostración
example
  (hP : ∀ n, P n)
  (hPQ : ∀ n, P (n-1) → Q n)
  : ∀ n, Q n :=
begin
  intro a,
  apply hPQ,
  exact hP (a-1),
end

-- 3ª demostración
example
  (hP : ∀ n, P n)
  (hPQ : ∀ n, P (n-1) → Q n)
  : ∀ n, Q n :=
begin
  intro a,
  exact hPQ a (hP (a-1)),
end

-- 4ª demostración
example
  (hP : ∀ n, P n)
  (hPQ : ∀ n, P (n-1) → Q n)
  : ∀ n, Q n :=
λ a, hPQ a (hP (a-1))

-- 5ª demostración
example
  (hP : ∀ n, P n)
  (hPQ : ∀ n, P (n-1) → Q n)
  : ∀ n, Q n :=
-- by hint
by tauto

-- 6ª demostración
example
  (hP : ∀ n, P n)
  (hPQ : ∀ n, P (n-1) → Q n)
  : ∀ n, Q n :=
by finish
