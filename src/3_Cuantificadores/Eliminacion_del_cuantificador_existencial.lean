-- Eliminación del cuantificador existencial
-- =========================================

variable (Q : Prop)
variable (P : ℕ → Prop)

-- ----------------------------------------------------
-- Ejercicio. Demostrar
--      ∀ n, P n → Q ⊢ (∃ n, P n) → Q
-- ----------------------------------------------------

-- 1ª demostración
example
  (hPQ : ∀ n, P n → Q)
  : (∃ n, P n) → Q :=
begin
  intro hP,
  cases hP with n₀ hn₀,
  specialize hPQ n₀,
  exact hPQ hn₀,
end

-- 2ª demostración
example
  (hPQ : ∀ n, P n → Q)
  : (∃ n, P n) → Q :=
begin
  intro hP,
  cases hP with n₀ hn₀,
  apply hPQ n₀,
  exact hn₀
end

-- 3ª demostración
example
  (hPQ : ∀ n, P n → Q)
  : (∃ n, P n) → Q :=
assume hP : ∃ n, P n,
exists.elim hP
  ( assume n₀,
    assume hn₀ : P n₀,
    show Q,
      from hPQ n₀ hn₀)

-- 4ª demostración
example
  (hPQ : ∀ n, P n → Q)
  : (∃ n, P n) → Q :=
assume hP : ∃ n, P n,
exists.elim hP
  ( assume n₀,
    assume hn₀ : P n₀,
    hPQ n₀ hn₀)

-- 5ª demostración
example
  (hPQ : ∀ n, P n → Q)
  : (∃ n, P n) → Q :=
assume hP : ∃ n, P n,
exists.elim hP
  ( λ n₀ hn₀, hPQ n₀ hn₀)

-- 6ª demostración
example
  (hPQ : ∀ n, P n → Q)
  : (∃ n, P n) → Q :=
λ hP, exists.elim hP (λ n₀ hn₀, hPQ n₀ hn₀)
