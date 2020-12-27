-- Si c es el límite de la sucesión u, entonces u(n) ≥ c/2 a partir de un N
-- ========================================================================

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
-- Ejercicio 3. Demostrar que si c > 0 y es  el límite
-- de la sucesión u, entonces u(n) ≥ c/2 a partir de un
-- N.
-- ----------------------------------------------------

-- 1ª demostración
example
  (hc : c > 0)
  (h : limite u c)
  : ∃ N, ∀ n ≥ N, u n ≥ c/2 :=
begin
  have h1 : c/2 > 0,
    by linarith,
  specialize h (c/2) h1,
  cases h with N hN,
  use N,
  intros n hn,
  specialize hN n hn,
  rw abs_le at hN,
  linarith,
end

-- 1ª demostración
example
  (hc : c > 0)
  (h : limite u c)
  : ∃ N, ∀ n ≥ N, u n ≥ c/2 :=
begin
  specialize h (c/2) (by linarith),
  cases h with N hN,
  use N,
  intros n hn,
  specialize hN n hn,
  rw abs_le at hN,
  linarith,
end

-- 3ª demostración
example
  (hc : c > 0)
  (h : limite u c)
  : ∃ N, ∀ n ≥ N, u n ≥ c/2 :=
begin
  cases h (c/2) (by linarith) with N hN,
  use N,
  intros n hn,
  specialize hN n hn,
  rw abs_le at hN,
  linarith,
end

-- 3ª demostración
example
  (hc : c > 0)
  (h : limite u c)
  : ∃ N, ∀ n ≥ N, u n ≥ c/2 :=
have h1 : c/2 > 0,
  by linarith,
have h2 : ∃ N, ∀ n, n ≥ N → |u n - c| ≤ c / 2,
  from h (c/2) h1,
exists.elim h2
  ( assume N,
    assume hN : ∀ n, n ≥ N → |u n - c| ≤ c / 2,
    have h3 : ∀ n ≥ N, u n ≥ c/2,
      { assume n,
        assume hn : n ≥ N,
        have h4 : -(c / 2) ≤ u n - c ∧ u n - c ≤ c / 2,
          from abs_le.mp (hN n hn),
        show u n ≥ c/2,
          from by linarith },
    show ∃ N, ∀ n ≥ N, u n ≥ c/2,
      from exists.intro N h3)
