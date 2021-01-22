-- Negación del universal: Caracterización de funciones no pares
-- =============================================================

import data.real.basic

variable (f : ℝ → ℝ)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    par : (ℝ → ℝ) → Prop
-- tal que (par f) expresa que f es par.
-- ----------------------------------------------------

def par : (ℝ → ℝ) → Prop
| f := ∀ x, f (-x) = f x

-- 1ª demostración
example : ¬par f ↔ ∃ x, f (-x) ≠ f x :=
begin
  split,
  { contrapose,
    intro h1,
    rw not_not,
    unfold par,
    intro x,
    by_contradiction h2,
    apply h1,
    use x, },
  { intro h1,
    intro h2,
    unfold par at h2,
    cases h1 with x hx,
    apply hx,
    exact h2 x, },
end

-- 2ª demostración
example : ¬par f ↔ ∃ x, f (-x) ≠ f x :=
begin
  split,
  { contrapose,
    intro h,
    rw not_not,
    intro x,
    by_contradiction H,
    apply h,
    use x, },
  { rintros ⟨x, hx⟩ h',
    exact hx (h' x) },
end

-- 3ª demostración
example : ¬par f ↔ ∃ x, f (-x) ≠ f x :=
iff.intro
  ( have h1 : ¬(∃ x, f (-x) ≠ f x) → ¬¬par f,
      { assume h2 : ¬(∃ x, f (-x) ≠ f x),
        have h3 : par f,
          { assume x,
            have h4 : ¬(f (-x) ≠ f x),
              { assume h5 : f (-x) ≠ f x,
                have h6 : ∃ x, f (-x) ≠ f x,
                  from exists.intro x h5,
                show false,
                  from h2 h6, },
            show f (-x) = f x,
              from not_not.mp h4},
        show ¬¬par f,
          from not_not.mpr h3 },
    show ¬par f → (∃ x, f (-x) ≠ f x),
      from not_imp_not.mp h1)
  ( assume h1 : ∃ x, f (-x) ≠ f x,
    show ¬par f,
      { assume h2 : par f,
        show false, from
          exists.elim h1
            ( assume x,
              assume hx : f (-x) ≠ f x,
              have h3 : f (-x) = f x,
                from h2 x,
              show false,
                from hx h3)})

-- 3ª demostración
example : ¬par f ↔ ∃ x, f (-x) ≠ f x :=
begin
  unfold par,
  push_neg,
end

-- 4ª demostración
example : ¬par f ↔ ∃ x, f (-x) ≠ f x :=
-- by suggest
not_forall

-- 5ª demostración
example : ¬par f ↔ ∃ x, f (-x) ≠ f x :=
-- by hint
by simp [par]
