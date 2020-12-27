-- Limite de la suma de dos sucesiones convergentes
-- ================================================

import data.real.basic

variables (u v : ℕ → ℝ)
variables (a b c : ℝ)

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
-- Ejercicio 3. Demostrar que si a es el límite de la
-- sucesión u y b el de la v, entonces el límite de
-- (u + v) es (a + b).
-- ----------------------------------------------------

-- 1ª demostración
example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
begin
  intros ε hε,
  have hε2 : 0 < ε / 2,
    { linarith },
  cases hu (ε / 2) hε2 with Nu hNu,
  cases hv (ε / 2) hε2 with Nv hNv,
  clear hu hv hε2 hε,
  use max Nu Nv,
  intros n hn,
  have hn₁ : n ≥ Nu,
    { exact le_of_max_le_left hn },
  specialize hNu n hn₁,
  have hn₂ : n ≥ Nv,
    { exact le_of_max_le_right hn },
  specialize hNv n hn₂,
  clear hn hn₁ hn₂ Nu Nv,
  calc |(u + v) n - (a + b)|
       = |u n + v n - (a + b)|    : rfl
   ... = |(u n - a) + (v n -  b)| : by { congr, ring }
   ... ≤ |u n - a| + |v n -  b|   : by apply abs_add
   ... ≤ ε / 2 + ε / 2            : by linarith
   ... = ε                        : by apply add_halves,
end

-- 1ª demostración
example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
begin
  intros ε hε,
  have hε2 : 0 < ε / 2,
    { linarith },
  cases hu (ε / 2) hε2 with Nu hNu,
  cases hv (ε / 2) hε2 with Nv hNv,
  clear hu hv hε2 hε,
  use max Nu Nv,
  intros n hn,
  have hn₁ : n ≥ Nu,
    { exact le_of_max_le_left hn },
  specialize hNu n hn₁,
  have hn₂ : n ≥ Nv,
    { exact le_of_max_le_right hn },
  specialize hNv n hn₂,
  clear hn hn₁ hn₂ Nu Nv,
  calc |(u + v) n - (a + b)|
       = |u n + v n - (a + b)|    : rfl
   ... = |(u n - a) + (v n -  b)| : by { congr, ring }
   ... ≤ |u n - a| + |v n -  b|   : by apply abs_add
   ... ≤ ε / 2 + ε / 2            : by linarith
   ... = ε                        : by apply add_halves,
end

-- 2ª demostración
-- ===============

lemma max_ge_iff
  {α : Type*}
  [linear_order α]
  {p q r : α}
  : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q :=
max_le_iff

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
begin
  intros ε hε,
  cases hu (ε/2) (by linarith) with Nu hNu,
  cases hv (ε/2) (by linarith) with Nv hNv,
  clear hu hv hε,
  use max Nu Nv,
  intros n hn,
  cases max_ge_iff.mp hn with hn₁ hn₂,
  have cota₁ : |u n - a| ≤ ε/2,
    from hNu n (by linarith),
  have cota₂ : |v n - b| ≤ ε/2,
    from hNv n (by linarith),
  calc |(u + v) n - (a + b)|
       = |u n + v n - (a + b)|   : rfl
   ... = |(u n - a) + (v n - b)| : by { congr, ring }
   ... ≤ |u n - a| + |v n - b|   : by apply abs_add
   ... ≤ ε                       : by linarith,
end
