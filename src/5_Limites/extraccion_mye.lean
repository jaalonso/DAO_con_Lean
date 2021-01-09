-- Las funciones de extracción no están acotadas
-- =============================================

import data.real.basic
open nat

variable {φ : ℕ → ℕ}

-- set_option pp.structure_projections false

-- ----------------------------------------------------
-- Nota. Se usará la siguiente definición y lema
-- estudiado anteriormente.
-- ----------------------------------------------------

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

-- ----------------------------------------------------
-- Ejercicio. Demostrar que las funciones de extracción
-- no está acotadas; es decir, que si φ es una función
-- de extracción, entonces
--     ∀ N N', ∃ n ≥ N', φ n ≥ N
-- ----------------------------------------------------

-- 1ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros N N',
  let n := max N N',
  use n,
  split,
  { exact le_max_right N N', },
  { calc N ≤ n   : le_max_left N N'
       ... ≤ φ n : id_mne_extraccion h n, },
end

-- 2ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros N N',
  let n := max N N',
  use n,
  split,
  { exact le_max_right N N', },
  { exact le_trans (le_max_left N N')
                   (id_mne_extraccion h n), },
end

-- 3ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros N N',
  use max N N',
  split,
  { exact le_max_right N N', },
  { exact le_trans (le_max_left N N')
                   (id_mne_extraccion h (max N N')), },
end

-- 4ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros N N',
  use max N N',
  exact ⟨le_max_right N N',
         le_trans (le_max_left N N')
                  (id_mne_extraccion h (max N N'))⟩,
end

-- 5ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
λ N N',
  ⟨max N N', ⟨le_max_right N N',
              le_trans (le_max_left N N')
                       (id_mne_extraccion h (max N N'))⟩⟩

-- 6ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
assume N N',
let n := max N N' in
have h1 : n ≥ N',
  from le_max_right N N',
show ∃ n ≥ N', φ n ≥ N, from
exists.intro n
  (exists.intro h1
    (show φ n ≥ N, from
       calc N ≤ n   : le_max_left N N'
          ... ≤ φ n : id_mne_extraccion h n))

-- 7ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
assume N N',
let n := max N N' in
have h1 : n ≥ N',
  from le_max_right N N',
show ∃ n ≥ N', φ n ≥ N, from
⟨n, h1, calc N ≤ n   : le_max_left N N'
          ...  ≤ φ n : id_mne_extraccion h n⟩

-- 8ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
assume N N',
let n := max N N' in
have h1 : n ≥ N',
  from le_max_right N N',
show ∃ n ≥ N', φ n ≥ N, from
⟨n, h1, le_trans (le_max_left N N')
                 (id_mne_extraccion h (max N N'))⟩

-- 9ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
assume N N',
let n := max N N' in
have h1 : n ≥ N',
  from le_max_right N N',
⟨n, h1, le_trans (le_max_left N N')
                 (id_mne_extraccion h n)⟩

-- 10ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
assume N N',
⟨max N N', le_max_right N N',
           le_trans (le_max_left N N')
                    (id_mne_extraccion h (max N N'))⟩

-- 11ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
λ N N',
  ⟨max N N', le_max_right N N',
             le_trans (le_max_left N N')
             (id_mne_extraccion h (max N N'))⟩
