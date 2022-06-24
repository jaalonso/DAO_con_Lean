-- Si a es un punto de acumulación de u, entonces ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-- ===================================================================================

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

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    punto_acumulacion : (ℕ → ℝ) → ℝ → Prop
-- tal que (punto_acumulacion u a) expresa que a es un
-- punto de acumulación de u; es decir, que es el
-- límite de alguna subsucesión de u.
-- ----------------------------------------------------

def punto_acumulacion : (ℕ → ℝ) → ℝ → Prop
| u a := ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar que si a es un punto de
-- acumulación de u, entonces
--    ∀ ε > 0, ∀ N, ∃ k ≥ N, |u k - a| ≤ ε
-- ----------------------------------------------------


-- 1ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
begin
  intros ε hε N,
  -- unfold punto_acumulacion at h,
  rcases h with ⟨φ, hφ1, hφ2⟩,
  -- unfold limite at hφ2,
  cases hφ2 ε hε with N' hN',
  rcases extraccion_mye hφ1 N N' with ⟨m, hm, hm'⟩,
  -- clear hφ1 hφ2,
  use φ m,
  split,
  { exact hm', },
  { exact hN' m hm, },
end

-- 2ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
begin
  intros ε hε N,
  rcases h with ⟨φ, hφ1, hφ2⟩,
  cases hφ2 ε hε with N' hN',
  rcases extraccion_mye hφ1 N N' with ⟨m, hm, hm'⟩,
  use φ m,
  exact ⟨hm', hN' m hm⟩,
end

-- 3ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
begin
  intros ε hε N,
  rcases h with ⟨φ, hφ1, hφ2⟩,
  cases hφ2 ε hε with N' hN',
  rcases extraccion_mye hφ1 N N' with ⟨m, hm, hm'⟩,
  exact ⟨φ m, hm', hN' _ hm⟩,
end

-- 4ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
begin
  intros ε hε N,
  rcases h with ⟨φ, hφ1, hφ2⟩,
  cases hφ2 ε hε with N' hN',
  rcases extraccion_mye hφ1 N N' with ⟨m, hm, hm'⟩,
  use φ m ; finish
end

-- 5ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| ≤ ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from extraccion_mye hφ.1 N N',
        exists.elim h1
          ( assume m,
            assume hm : ∃ (H : m ≥ N'), φ m ≥ N,
            exists.elim hm
              ( assume hm1 : m ≥ N',
                assume hm2 : φ m ≥ N,
                have h2 : |u (φ m) - a| ≤ ε,
                  from hN' m hm1,
                show ∃ n ≥ N, |u n - a| ≤ ε,
                  from exists.intro (φ m) (exists.intro hm2 h2)))))

-- 6ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| ≤ ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from extraccion_mye hφ.1 N N',
        exists.elim h1
          ( assume m,
            assume hm : ∃ (H : m ≥ N'), φ m ≥ N,
            exists.elim hm
              ( assume hm1 : m ≥ N',
                assume hm2 : φ m ≥ N,
                have h2 : |u (φ m) - a| ≤ ε,
                  from hN' m hm1,
                show ∃ n ≥ N, |u n - a| ≤ ε,
                  from ⟨φ m, hm2, h2⟩))))

-- 7ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| ≤ ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from extraccion_mye hφ.1 N N',
        exists.elim h1
          ( assume m,
            assume hm : ∃ (H : m ≥ N'), φ m ≥ N,
            exists.elim hm
              ( assume hm1 : m ≥ N',
                assume hm2 : φ m ≥ N,
                have h2 : |u (φ m) - a| ≤ ε,
                  from hN' m hm1,
                ⟨φ m, hm2, h2⟩))))

-- 8ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| ≤ ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from extraccion_mye hφ.1 N N',
        exists.elim h1
          ( assume m,
            assume hm : ∃ (H : m ≥ N'), φ m ≥ N,
            exists.elim hm
              ( assume hm1 : m ≥ N',
                assume hm2 : φ m ≥ N,
                ⟨φ m, hm2, hN' m hm1⟩))))

-- 9ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| ≤ ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from extraccion_mye hφ.1 N N',
        exists.elim h1
          ( assume m,
            assume hm : ∃ (H : m ≥ N'), φ m ≥ N,
            exists.elim hm
              (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))

-- 10ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| ≤ ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from extraccion_mye hφ.1 N N',
        exists.elim h1
          (λ m hm, exists.elim hm (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))

-- 11ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| ≤ ε,
        exists.elim (extraccion_mye hφ.1 N N')
          (λ m hm, exists.elim hm (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))

-- 12ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      (λ N' hN', exists.elim (extraccion_mye hφ.1 N N')
        (λ m hm, exists.elim hm
          (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))

-- 13ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  (λ φ hφ, exists.elim (hφ.2 ε hε)
    (λ N' hN', exists.elim (extraccion_mye hφ.1 N N')
      (λ m hm, exists.elim hm
        (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))

-- 14ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
λ ε hε N, exists.elim h
  (λ φ hφ, exists.elim (hφ.2 ε hε)
    (λ N' hN', exists.elim (extraccion_mye hφ.1 N N')
      (λ m hm, exists.elim hm
        (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))
