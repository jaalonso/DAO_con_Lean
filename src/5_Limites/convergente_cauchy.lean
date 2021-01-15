-- Toda sucesión convergente es una sucesión de Cauchy
-- ===================================================

import data.real.basic

variable {u : ℕ → ℝ}

-- ----------------------------------------------------
-- Nota. Usaremos los siguientes conceptos estudiados
-- anteriormente.
-- ----------------------------------------------------

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    sucesion_convergente : (ℕ → ℝ) → Prop
-- tal que (sucesion_convergente u) expresa que la
-- sucesión u es convergente.
-- ----------------------------------------------------

def sucesion_convergente : (ℕ → ℝ) → Prop
| u := ∃ a, limite u a

-- ----------------------------------------------------
-- Ejercicio 2. Definir la función
--    sucesion_de_Cauchy : (ℕ → ℝ) → Prop
-- tal que (sucesion_de_Cauchy u) expresa que la
-- sucesión u es una sucesión de Cauchy.
-- ----------------------------------------------------

def sucesion_de_Cauchy : (ℕ → ℝ) → Prop
| u := ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

-- ----------------------------------------------------
-- Ejercicio 3. Demostrar que toda sucesión convergente
-- es una sucesión de Cauchy.
-- ----------------------------------------------------

-- 1ª demostración
example
  (h : sucesion_convergente u)
  : sucesion_de_Cauchy u :=
begin
  -- unfold sucesion_convergente at h,
  cases h with a ha,
  -- unfold sucesion_de_Cauchy,
  intros ε hε,
  -- unfold limite at ha,
  cases ha (ε/2) (half_pos hε) with N hN,
  use N,
  intros p q hp hq,
  calc  |u p - u q|
      = |(u p - a) + (a - u q)| : by ring
  ... ≤ |u p - a| + |a - u q|   : by apply abs_add
  ... = |u p - a| + |u q - a|   : by rw abs_sub (u q) a
  ... ≤ ε/2 + |u q - a|         : add_le_add_right (hN p hp) _
  ... ≤ ε/2 + ε/2               : add_le_add_left (hN q hq) (ε/2)
  ... = ε                       : add_halves ε
end

-- 2ª demostración
example
  (h : sucesion_convergente u)
  : sucesion_de_Cauchy u :=
begin
  cases h with a ha,
  intros ε hε,
  cases ha (ε/2) (by linarith) with N hN,
  use N,
  intros p q hp hq,
  calc  |u p - u q|
      = |(u p - a) + (a - u q)| : by ring
  ... ≤ |u p - a| + |a - u q|   : by simp only [abs_add]
  ... = |u p - a| + |u q - a|   : by simp only [abs_add, abs_sub]
  ... ≤ ε                       : by linarith [hN p hp, hN q hq],
end

-- 3ª demostración
example
  (h : sucesion_convergente u)
  : sucesion_de_Cauchy u :=
exists.elim h
  (assume a,
   assume ha : limite u a,
   show sucesion_de_Cauchy u, from
     (assume ε,
      assume hε : ε > 0,
      exists.elim (ha (ε/2) (by linarith))
        (assume N,
         assume hN : ∀ n, n ≥ N → |u n - a| ≤ ε/2,
         show ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε,
           from exists.intro N
             (assume p q,
              assume hp: p ≥ N,
              assume hq: q ≥ N,
              show |u p - u q| ≤ ε, from
                calc  |u p - u q|
                    = |(u p - a) + (a - u q)| : by ring
                ... ≤ |u p - a| + |a - u q|   : by simp only [abs_add]
                ... = |u p - a| + |u q - a|   : by simp only [abs_add, abs_sub]
                ... ≤ ε                       : by linarith [hN p hp, hN q hq]))))
