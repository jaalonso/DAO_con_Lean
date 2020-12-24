-- Propiedad: ∃ k, n = k + 1 ⊢ n > 0
-- =================================

import tactic

variable (n : ℕ)

-- ----------------------------------------------------
-- Ejercicio. Demostrar que si
--    ∃ k, n = k + 1
-- entonces
--    n > 0
-- ----------------------------------------------------

-- 1ª demostración
example
  (h : ∃ k : ℕ, n = k + 1)
  : n > 0 :=
begin
  cases h with k₀ hk₀,
  rw hk₀,
  exact nat.succ_pos k₀,
end

-- 2ª demostración
example
  (h : ∃ k : ℕ, n = k + 1)
  : n > 0 :=
begin
  cases h with k₀ hk₀,
  rw hk₀,
  linarith,
end

-- 3ª demostración
example
  (h : ∃ k : ℕ, n = k + 1)
  : n > 0 :=
begin
  cases h,
  linarith,
end

-- 4ª demostración
example
  (h : ∃ k : ℕ, n = k + 1)
  : n > 0 :=
exists.elim h
 ( assume k₀,
   assume hk₀ : n = k₀ + 1,
   show n > 0, from
     calc n = k₀ + 1 : hk₀
      ...   > 0      : nat.succ_pos k₀)

-- 5ª demostración
example
  (h : ∃ k : ℕ, n = k + 1)
  : n > 0 :=
exists.elim h
 ( assume k₀,
   assume hk₀ : n = k₀ + 1,
   show n > 0, from
     calc n = k₀ + 1 : hk₀
      ...   > 0      : by linarith)

-- 5ª demostración
example
  (h : ∃ k : ℕ, n = k + 1)
  : n > 0 :=
exists.elim h (λ _ _, by linarith)
