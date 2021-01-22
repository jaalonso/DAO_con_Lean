-- Pruebas de ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k
-- =========================================

import tactic

variable (n : ℤ)

-- ----------------------------------------------------
-- Ejercicio. Demostrar que si n es un número entero,
-- entonces
--    ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k
-- ----------------------------------------------------

-- 1ª demostración
example : ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
begin
  split,
  { intro h,
    intro k,
    intro hk,
    apply h,
    use k,
    exact hk, },
  { intro h1,
    intro h2,
    cases h2 with k hk,
    apply h1 k,
    exact hk, },
end

-- 2ª demostración
example : ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
begin
  split,
  { intros h k hk,
    exact h ⟨k, hk⟩ },
  { rintros h ⟨k, rfl⟩,
    apply h k,
    refl, },
end

-- 3ª demostración
example : ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
begin
  split,
  { intros h k hk,
    exact h ⟨k, hk⟩ },
  { rintros h ⟨k, rfl⟩,
    exact h k rfl },
end

-- 4ª demostración
example : ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
begin
  push_neg,
end

-- 5ª demostración
example : ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
by push_neg

-- 6ª demostración
example : ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
iff.intro
  ( assume h1 : ¬(∃ k, n = 2*k),
    show ∀ k, n ≠ 2*k, from
      assume k,
      show n ≠ 2*k, from
        assume h2 : n = 2*k,
        have h3 : ∃ k, n = 2*k,
          from exists.intro k h2,
        show false,
          from h1 h3)
  ( assume h1 : ∀ k, n ≠ 2*k,
    show ¬(∃ k, n = 2*k), from
      assume h2 : ∃ k, n = 2*k,
      show false, from
        exists.elim h2
          ( assume k,
            assume hk : n = 2*k,
            have h3 : n ≠ 2*k,
              from h1 k,
            show false,
              from h3 hk))

-- 7ª demostración
example : ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
iff.intro
  ( assume h1 : ¬(∃ k, n = 2*k),
    show ∀ k, n ≠ 2*k, from
      assume k,
      show n ≠ 2*k, from
        assume h2 : n = 2*k,
        have h3 : ∃ k, n = 2*k,
          from exists.intro k h2,
        h1 h3)
  ( assume h1 : ∀ k, n ≠ 2*k,
    show ¬(∃ k, n = 2*k), from
      assume h2 : ∃ k, n = 2*k,
      show false, from
        exists.elim h2
          ( assume k,
            assume hk : n = 2*k,
            have h3 : n ≠ 2*k,
              from h1 k,
            h3 hk))

-- 8ª demostración
example : ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
iff.intro
  ( assume h1 : ¬(∃ k, n = 2*k),
    show ∀ k, n ≠ 2*k, from
      assume k,
      show n ≠ 2*k, from
        assume h2 : n = 2*k,
        h1 (exists.intro k h2))
  ( assume h1 : ∀ k, n ≠ 2*k,
    show ¬(∃ k, n = 2*k), from
      assume h2 : ∃ k, n = 2*k,
      show false, from
        exists.elim h2
          ( assume k,
            assume hk : n = 2*k,
            (h1 k) hk))

-- 9ª demostración
example : ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
iff.intro
  ( assume h1 : ¬(∃ k, n = 2*k),
    show ∀ k, n ≠ 2*k, from
      assume k,
      λ h2, h1 (exists.intro k h2))
  ( assume h1 : ∀ k, n ≠ 2*k,
    show ¬(∃ k, n = 2*k), from
      assume h2 : ∃ k, n = 2*k,
      show false, from
        exists.elim h2
          (λ k hk, (h1 k) hk))

-- 10ª demostración
example : ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
iff.intro
  ( assume h1 : ¬(∃ k, n = 2*k),
    λ k, λ h2, h1 (exists.intro k h2))
  ( assume h1 : ∀ k, n ≠ 2*k,
    show ¬(∃ k, n = 2*k), from
      assume h2 : ∃ k, n = 2*k,
      exists.elim h2 (λ k hk, (h1 k) hk))

-- 11ª demostración
example : ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
iff.intro
  (λ h1 k h2, h1 (exists.intro k h2))
  (λ h1 h2, exists.elim h2 (λ k hk, (h1 k) hk))

-- 12ª demostración
example : ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
⟨λ h1 k h2, h1 ⟨k, h2⟩,
 λ h1 h2, exists.elim h2 (λ k hk, (h1 k) hk)⟩

-- 13ª demostración
example : ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
-- by hint
by simp

-- 14ª demostración
example : ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
by finish

-- 15ª demostración
example : ¬(∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
by norm_num
