-- Si a es un punto de acumulación de la sucesión de Cauchy u, entonces a es el límite de u
-- ========================================================================================

import data.real.basic

variable  {u : ℕ → ℝ}
variables {a : ℝ}
variable  {φ : ℕ → ℕ}

-- ----------------------------------------------------
-- Nota. Usaremos los siguientes conceptos estudiados
-- anteriormente.
-- ----------------------------------------------------

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε

def extraccion : (ℕ → ℕ) → Prop
| φ := ∀ n m, n < m → φ n < φ m

lemma id_mne_extraccion
  (h : extraccion φ)
  : ∀ n, n ≤ φ n :=
begin
  intros n,
  induction n with m HI,
  { linarith },
  { exact nat.succ_le_of_lt (by linarith [h m (m+1) (by linarith)]) },
end

lemma extraccion_mye
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
λ N N',
  ⟨max N N', le_max_right N N',
             le_trans (le_max_left N N')
             (id_mne_extraccion h (max N N'))⟩

def punto_acumulacion : (ℕ → ℝ) → ℝ → Prop
| u a := ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

lemma cerca_acumulacion
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
begin
  intros ε hε N,
  rcases h with ⟨φ, hφ1, hφ2⟩,
  cases hφ2 ε hε with N' hN',
  rcases extraccion_mye hφ1 N N' with ⟨m, hm, hm'⟩,
  exact ⟨φ m, hm', hN' _ hm⟩,
end

def sucesion_de_Cauchy : (ℕ → ℝ) → Prop
| u := ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

-- ----------------------------------------------------
-- Ejercicio. Demostrar que si u es una sucesión de
-- Cauchy y a es un punto de acumulación de u, entonces
-- a es el límite de u.
-- ----------------------------------------------------

-- 1ª demostración
example
  (hu : sucesion_de_Cauchy u)
  (ha : punto_acumulacion u a)
  : limite u a :=
begin
  -- unfold limite,
  intros ε hε,
  -- unfold sucesion_de_Cauchy at hu,
  cases hu (ε/2) (half_pos hε) with N hN,
  use N,
  have ha' : ∃ N' ≥ N, |u N' - a| ≤ ε/2,
    apply cerca_acumulacion ha (ε/2) (half_pos hε),
  cases ha' with N' h,
  cases h with hNN' hN',
  intros n hn,
  calc   |u n - a|
       = |(u n - u N') + (u N' - a)| : by ring
   ... ≤ |u n - u N'| + |u N' - a|   : abs_add (u n - u N') (u N' - a)
   ... ≤ ε/2 + |u N' - a|            : add_le_add_right (hN n N' hn hNN') _
   ... ≤ ε/2 + ε/2                   : add_le_add_left hN' (ε / 2)
   ... = ε                           : add_halves ε
end

-- 2ª demostración
example
  (hu : sucesion_de_Cauchy u)
  (ha : punto_acumulacion u a)
  : limite u a :=
begin
  intros ε hε,
  cases hu (ε/2) (by linarith) with N hN,
  use N,
  have ha' : ∃ N' ≥ N, |u N' - a| ≤ ε/2,
    apply cerca_acumulacion ha (ε/2) (by linarith),
  rcases ha' with ⟨N', hNN', hN'⟩,
  intros n hn,
  calc  |u n - a|
      = |(u n - u N') + (u N' - a)| : by ring
  ... ≤ |u n - u N'| + |u N' - a|   : by simp [abs_add]
  ... ≤ ε                           : by linarith [hN n N' hn hNN'],
end
