-- Unicidad del límite de las sucesiones convergentes
-- ==================================================

import data.real.basic

variables (u : ℕ → ℝ)
variables (a b x y : ℝ)

-- ----------------------------------------------------
-- Nota. Se usarán las siguientes notaciones,
-- definiciones y lemas estudiados anteriormente:
-- + |x| = abs x
-- + limite u c :
--      ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε
-- + cero_de_abs_mn_todos:
--      (∀ ε > 0, |x| ≤ ε) → x = 0
-- + ig_de_abs_sub_mne_todos:
--      (∀ ε > 0, |x - y| ≤ ε) → x = y
-- ----------------------------------------------------

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε

lemma cero_de_abs_mn_todos
  (h : ∀ ε > 0, |x| ≤ ε)
  : x = 0 :=
abs_eq_zero.mp
  (eq_of_le_of_forall_le_of_dense (abs_nonneg x) h)

lemma ig_de_abs_sub_mne_todos
  (h : ∀ ε > 0, |x - y| ≤ ε)
  : x = y :=
sub_eq_zero.mp (cero_de_abs_mn_todos (x - y) h)

-- ----------------------------------------------------
-- Ejercicio. Demostrar que cada sucesión tiene como
-- máximo un límite.
-- ----------------------------------------------------

-- 1ª demostración
example
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
begin
  apply ig_de_abs_sub_mne_todos,
  intros ε hε,
  cases ha (ε/2) (half_pos hε) with Na hNa,
  cases hb (ε/2) (half_pos hε) with Nb hNb,
  let N := max Na Nb,
  clear ha hb,
  specialize hNa N (le_max_left  _ _),
  specialize hNb N (le_max_right  _ _),
  calc |a - b|
       = |(a - u N) + (u N - b)| : by ring
   ... ≤ |a - u N| + |u N - b|   : by apply abs_add
   ... = |u N - a| + |u N - b|   : by rw abs_sub
   ... ≤ ε/2 + ε/2               : add_le_add hNa hNb
   ... = ε                       : add_halves ε
end

-- 2ª demostración
example
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
begin
  apply ig_de_abs_sub_mne_todos,
  intros ε hε,
  cases ha (ε/2) (by linarith) with Na hNa,
  cases hb (ε/2) (by linarith) with Nb hNb,
  let N := max Na Nb,
  clear ha hb,
  specialize hNa N (by finish),
  specialize hNb N (by finish),
  calc |a - b|
       = |(a - u N) + (u N - b)| : by ring
   ... ≤ |a - u N| + |u N - b|   : by apply abs_add
   ... = |u N - a| + |u N - b|   : by rw abs_sub
   ... ≤ ε                       : by linarith [hNa, hNb]
end
