-- Los supremos de las sucesiones no decrecientes son sus límites
-- ==============================================================

import data.real.basic

variable (u : ℕ → ℝ)
variable (M : ℝ)

-- ----------------------------------------------------
-- Nota. Se usarán las siguientes notaciones y
-- definiciones estudiadas anteriormente:
-- + |x| = abs x
-- + limite u c :
--      ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε
-- ----------------------------------------------------

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    no_decreciente : (ℕ → ℝ) → Prop
-- tal que (no_decreciente) expresa que la sucesión u
-- es no decreciente.
-- ----------------------------------------------------

def no_decreciente : (ℕ → ℝ) → Prop
| u := ∀ n m, n ≤ m → u n ≤ u m

-- ----------------------------------------------------
-- Ejercicio 2. Definir la función
--    es_sup_suc : ℝ → (ℕ → ℝ) → Prop
-- tal que (es_sup_suc M u) expresa que M es el supremo
-- de la sucesión u.
-- ----------------------------------------------------

def es_sup_suc : ℝ → (ℕ → ℝ) → Prop
| M u := (∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

-- ----------------------------------------------------
-- Ejercicio 3. Demostrar que si M es un supremo de la
-- sucesión no decreciente u, entonces el límite de u
-- es M.
-- ----------------------------------------------------

-- 1ª demostración
example
  (h : es_sup_suc M u)
  (h' : no_decreciente u)
  : limite u M :=
begin
  -- unfold limite,
  intros ε hε,
  -- unfold es_sup_suc at h,
  cases h with hM₁ hM₂,
  cases hM₂ ε hε with n₀ hn₀,
  use n₀,
  intros n hn,
  rw abs_le,
  split,
  { -- unfold no_decreciente at h',
    specialize h' n₀ n hn,
    calc -ε
         = (M - ε) - M : by ring
     ... ≤ u n₀ - M    : sub_le_sub_right hn₀ M
     ... ≤ u n - M     : sub_le_sub_right h' M },
  { calc u n - M
         ≤ M - M       : sub_le_sub_right (hM₁ n) M
     ... = 0           : sub_self M
     ... ≤ ε           : le_of_lt hε, },
end

-- 2ª demostración
example
  (h : es_sup_suc M u)
  (h' : no_decreciente u)
  : limite u M :=
begin
  intros ε hε,
  cases h with hM₁ hM₂,
  cases hM₂ ε hε with n₀ hn₀,
  use n₀,
  intros n hn,
  rw abs_le,
  split,
  { linarith [h' n₀ n hn] },
  { linarith [hM₁ n] },
end

-- 3ª demostración
example
  (h : es_sup_suc M u)
  (h' : no_decreciente u)
  : limite u M :=
begin
  intros ε hε,
  cases h with hM₁ hM₂,
  cases hM₂ ε hε with n₀ hn₀,
  use n₀,
  intros n hn,
  rw abs_le,
  split ; linarith [h' n₀ n hn, hM₁ n],
end

-- 4ª demostración
example
  (h : es_sup_suc M u)
  (h' : no_decreciente u)
  : limite u M :=
assume ε,
assume hε : ε > 0,
have hM₁ : ∀ (n : ℕ), u n ≤ M,
  from h.left,
have hM₂ : ∀ (ε : ℝ), ε > 0 → (∃ (n₀ : ℕ), u n₀ ≥ M - ε),
  from h.right,
exists.elim (hM₂ ε hε)
  ( assume n₀,
    assume hn₀ : u n₀ ≥ M - ε,
    have h1 : ∀ n, n ≥ n₀ → |u n - M| ≤ ε,
      { assume n,
        assume hn : n ≥ n₀,
        have h2 : -ε ≤ u n - M,
          { have h'a : u n₀ ≤ u n,
              from h' n₀ n hn,
            calc -ε
                 = (M - ε) - M : by ring
             ... ≤ u n₀ - M    : sub_le_sub_right hn₀ M
             ... ≤ u n - M     : sub_le_sub_right h'a M },
        have h3 : u n - M ≤ ε,
          { calc u n - M
                 ≤ M - M       : sub_le_sub_right (hM₁ n) M
             ... = 0           : sub_self M
             ... ≤ ε           : le_of_lt hε },
        show |u n - M| ≤ ε,
          from abs_le.mpr (and.intro h2 h3) },
    show ∃ N, ∀ n, n ≥ N → |u n - M| ≤ ε,
      from exists.intro n₀ h1)
