-- Límite de subsucesiones
-- =======================

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
-- Ejercicio. Demostrar que las subsucesiones de las
-- sucesiones convergentes tienen el mismo límite que
-- la sucesión.
-- ----------------------------------------------------

-- 1ª demostración
example
  (h : limite u a)
  (hφ : extraccion φ)
  : limite (u ∘ φ) a :=
begin
  -- unfold limite,
  intros ε hε,
  -- unfold limite at h,
  cases h ε hε with N hN,
  use N,
  intros n hn,
  apply hN,
  apply le_trans hn,
  exact id_mne_extraccion hφ n,
end

-- 2ª demostración
example
  (h : limite u a)
  (hφ : extraccion φ)
  : limite (u ∘ φ) a :=
begin
  intros ε hε,
  cases h ε hε with N hN,
  use N,
  intros n hn,
  apply hN,
  exact le_trans hn (id_mne_extraccion hφ n),
end

-- 3ª demostración
example
  (h : limite u a)
  (hφ : extraccion φ)
  : limite (u ∘ φ) a :=
begin
  intros ε hε,
  cases h ε hε with N hN,
  use N,
  intros n hn,
  exact hN (φ n) (le_trans hn (id_mne_extraccion hφ n)),
end

-- 4ª demostración
example
  (h : limite u a)
  (hφ : extraccion φ)
  : limite (u ∘ φ) a :=
begin
  intros ε hε,
  cases h ε hε with N hN,
  use N,
  exact λ n hn, hN (φ n) (le_trans hn (id_mne_extraccion hφ n)),
end

-- 5ª demostración
example
  (h : limite u a)
  (hφ : extraccion φ)
  : limite (u ∘ φ) a :=
begin
  intros ε hε,
  -- unfold limite at h,
  cases h ε hε with N hN,
  exact ⟨N, λ n hn, hN (φ n) (le_trans hn (id_mne_extraccion hφ n))⟩,
end

-- 6ª demostración
example
  (h : limite u a)
  (hφ : extraccion φ)
  : limite (u ∘ φ) a :=
begin
  intros ε hε,
  exact (exists.elim (h ε hε)
          (λ N hN,
            ⟨N, λ n hn,
                  hN (φ n) (le_trans hn (id_mne_extraccion hφ n))⟩)),
end

-- 7ª demostración
example
  (h : limite u a)
  (hφ : extraccion φ)
  : limite (u ∘ φ) a :=
λ ε hε,
  (exists.elim (h ε hε)
    (λ N hN,
       ⟨N, λ n hn,
             hN (φ n) (le_trans hn (id_mne_extraccion hφ n))⟩))

-- 8ª demostración
example
  (h : limite u a)
  (hφ : extraccion φ)
  : limite (u ∘ φ) a :=
begin
  intros ε hε,
  cases h ε hε with N hN,
  use N,
  intros n hn,
  apply hN,
  calc N ≤ n   : hn
     ... ≤ φ n : id_mne_extraccion hφ n,
end

-- 9ª demostración
lemma limite_subsucesion
  (h : limite u a)
  (hφ : extraccion φ)
  : limite (u ∘ φ) a :=
assume ε,
assume hε : ε > 0,
exists.elim (h ε hε)
 ( assume N,
   assume hN : ∀ n, n ≥ N → |u n - a| ≤ ε,
   have h1 : ∀n, n ≥ N → |(u ∘ φ) n - a| ≤ ε,
     { assume n,
       assume hn : n ≥ N,
       have h2 : N ≤ φ n, from
         calc N ≤ n   : hn
           ... ≤ φ n : id_mne_extraccion hφ n,
       show |(u ∘ φ) n - a| ≤ ε,
         from hN (φ n) h2,
     },
   show ∃ N, ∀n, n ≥ N → |(u ∘ φ) n - a| ≤ ε,
     from exists.intro N h1)
