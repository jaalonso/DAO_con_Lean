-- La función identidad no está acotada superiormente
-- ==================================================

import data.real.basic

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    acotada_superiormente : (ℝ → ℝ) → Prop
-- tal que (acotada_superiormente f) expresa que la
-- función f está acotada superiormente.
-- ----------------------------------------------------

def acotada_superiormente : (ℝ → ℝ) → Prop
| f := ∃ M, ∀ x, f x ≤ M

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar que la función identidad no
-- está acotada superiormente.
-- ----------------------------------------------------

-- 1ª demostración
example : ¬acotada_superiormente id :=
begin
  unfold acotada_superiormente,
  unfold id,
  by_contradiction h,
  cases h with M hM,
  specialize hM (M+1),
  contrapose hM,
  simp only [not_le],
  exact lt_add_one M,
end

-- 2ª demostración
example : ¬acotada_superiormente id :=
begin
  unfold acotada_superiormente id,
  push_neg,
  intro M,
  use M + 1,
  linarith,
end

-- 3ª demostración
example : ¬acotada_superiormente id :=
begin
  unfold acotada_superiormente id,
  push_neg,
  exact no_top,
end

-- 4ª demostración
example : ¬acotada_superiormente id :=
assume h1 : acotada_superiormente id,
have h2 : ∃ M, ∀ x, id x ≤ M,
  from h1,
show false, from
  exists.elim h2
    ( assume M,
      assume hM : ∀ x, id x ≤ M,
      have h3 : M + 1 ≤ M,
        from hM (M+1),
      have h4 : ¬(M < M + 1),
        from not_lt.mpr h3,
      have h5 : M < M + 1,
        from lt_add_one M,
      show false,
        from h4 h5)

-- 5ª demostración
example : ¬acotada_superiormente id :=
assume h1 : acotada_superiormente id,
have h2 : ∃ M, ∀ x, id x ≤ M,
  from h1,
show false, from
  exists.elim h2
    ( assume M,
      assume hM : ∀ x, id x ≤ M,
      have h3 : M + 1 ≤ M,
        from hM (M+1),
      have h4 : ¬(M < M + 1),
        from not_lt.mpr h3,
      have h5 : M < M + 1,
        from lt_add_one M,
      h4 h5)

-- 6ª demostración
example : ¬acotada_superiormente id :=
assume h1 : acotada_superiormente id,
have h2 : ∃ M, ∀ x, id x ≤ M,
  from h1,
show false, from
  exists.elim h2
    ( assume M,
      assume hM : ∀ x, id x ≤ M,
      have h3 : M + 1 ≤ M,
        from hM (M+1),
      (not_lt.mpr h3) (lt_add_one M))

-- 7ª demostración
example : ¬acotada_superiormente id :=
assume h1 : acotada_superiormente id,
have h2 : ∃ M, ∀ x, id x ≤ M,
  from h1,
show false, from
  exists.elim h2
    ( assume M,
      assume hM : ∀ x, id x ≤ M,
      (not_lt.mpr (hM (M+1))) (lt_add_one M))

-- 8ª demostración
example : ¬acotada_superiormente id :=
assume h1 : acotada_superiormente id,
have h2 : ∃ M, ∀ x, id x ≤ M,
  from h1,
show false, from
  exists.elim h2
    (λ M hM, (not_lt.mpr (hM (M+1))) (lt_add_one M))

-- 9ª demostración
example : ¬acotada_superiormente id :=
assume h1 : acotada_superiormente id,
have h2 : ∃ M, ∀ x, id x ≤ M,
  from h1,
exists.elim h2
  (λ M hM, (not_lt.mpr (hM (M+1))) (lt_add_one M))

-- 10ª demostración
example : ¬acotada_superiormente id :=
assume h1 : acotada_superiormente id,
exists.elim h1
  (λ M hM, (not_lt.mpr (hM (M+1))) (lt_add_one M))

-- 11ª demostración
example : ¬acotada_superiormente id :=
λ h1, exists.elim h1 (λ M hM, (not_lt.mpr (hM (M+1))) (lt_add_one M))
