-- Propiedad: Si (g ∘ f) es suprayectiva, entonces g es suprayectiva
-- =================================================================

import data.real.basic
open function

variables (f g : ℝ → ℝ)

-- #print surjective
-- #print notation (∘)

-- ----------------------------------------------------
-- Ejercicio. Demostrar que si (g ∘ f) es suprayectiva,
-- entonces g también lo es
-- ----------------------------------------------------

-- 1ª demostración
example
  (h : surjective (g ∘ f))
  : surjective g :=
begin
  -- unfold surjective at *,
  intro y,
  specialize h y,
  cases h with x hx,
  -- unfold comp at hx,
  use f x,
  exact hx,
end

-- 2ª demostración
example
  (h : surjective (g ∘ f))
  : surjective g :=
begin
  intro y,
  specialize h y,
  cases h with x hx,
  exact ⟨f x, hx⟩,
end

-- 3ª demostración
example
  (h : surjective (g ∘ f))
  : surjective g :=
begin
  intro y,
  cases h y with x hx,
  rw ← hx,
  use f x,
end

-- 4ª demostración
example
  (h : surjective (g ∘ f))
  : surjective g :=
begin
  intro y,
  rcases h y with ⟨x, rfl⟩,
  use f x,
end

-- 5ª demostración
example
  (h : surjective (g ∘ f))
  : surjective g :=
assume y,
have h1 : ∃ a, (g ∘ f) a = y,
  from h y,
exists.elim h1
  ( assume x,
    assume hx : (g ∘ f) x = y,
    show ∃ a, g a = y,
      from exists.intro (f x) hx)

-- 6ª demostración
example
  (h : surjective (g ∘ f))
  : surjective g :=
assume y,
have h1 : ∃ a, (g ∘ f) a = y,
  from h y,
exists.elim h1
  ( assume x,
    assume hx : (g ∘ f) x = y,
    exists.intro (f x) hx)

-- 7ª demostración
example
  (h : surjective (g ∘ f))
  : surjective g :=
assume y,
have h1 : ∃ a, (g ∘ f) a = y,
  from h y,
exists.elim h1
  (λ x hx, exists.intro (f x) hx)

-- 8ª demostración
example
  (h : surjective (g ∘ f))
  : surjective g :=
assume y,
exists.elim (h y)
  (λ x hx, exists.intro (f x) hx)

-- 9ª demostración
example
  (h : surjective (g ∘ f))
  : surjective g :=
λ y, exists.elim (h y) (λ x hx, exists.intro (f x) hx)

-- 10ª demostración
example
  (h : surjective (g ∘ f))
  : surjective g :=
λ y, exists.elim (h y) (λ x hx, ⟨f x, hx⟩)

-- 11ª demostración
example
  (h : surjective (g ∘ f))
  : surjective g :=
-- by library_search
surjective.of_comp h

-- 12ª demostración
example
  (h : surjective (g ∘ f))
  : surjective g :=
λ y, let ⟨x, hx⟩ := h y in ⟨f x, hx⟩
