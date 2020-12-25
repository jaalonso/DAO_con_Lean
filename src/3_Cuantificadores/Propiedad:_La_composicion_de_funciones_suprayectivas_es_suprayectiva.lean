-- La composición de funciones suprayectivas es suprayectiva
-- =========================================================


import data.real.basic

open function

variables (f g : ℝ → ℝ)

-- ----------------------------------------------------
-- Ejercicio. Demostrar que si f y g son suprayectivas,
-- entonces también los es su composición.
-- ----------------------------------------------------

-- 1ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
begin
  intro z,
  cases hg z with y hy,
  rw ← hy,
  cases hf y with x hx,
  rw ← hx,
  use x,
end

-- 2ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
begin
  intro z,
  rcases hg z with ⟨y, rfl⟩,
  rcases hf y with ⟨x, rfl⟩,
  use x,
end

-- 3ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
assume z,
exists.elim (hg z)
  ( assume y,
    assume hy : g y = z,
    exists.elim (hf y)
      ( assume x,
        assume hx : f x = y,
        show ∃ a, (g ∘ f) a = z,
          from exists.intro x
                ( have h1 : (g ∘ f) x = g y,
                    from congr_arg g hx,
                  show (g ∘ f) x = z,
                    from eq.trans h1 hy)))

-- 4ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
assume z,
exists.elim (hg z)
  ( assume y,
    assume hy : g y = z,
    exists.elim (hf y)
      ( assume x,
        assume hx : f x = y,
        show ∃ a, (g ∘ f) a = z,
          from exists.intro x
                ( show g (f x) = z,
                    from eq.trans (congr_arg g hx) hy)))

-- 5ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
assume z,
exists.elim (hg z)
  ( assume y,
    assume hy : g y = z,
    exists.elim (hf y)
      ( assume x,
        assume hx : f x = y,
        exists.intro x (show g (f x) = z, from eq.trans (congr_arg g hx) hy)))

-- 6ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
assume z,
exists.elim (hg z)
  ( assume y,
    assume hy : g y = z,
    exists.elim (hf y)
      (λ x hx, exists.intro x (show g (f x) = z, from eq.trans (congr_arg g hx) hy)))

-- 7ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
assume z,
exists.elim (hg z)
  (λ y hy, exists.elim (hf y)
             (λ x hx, exists.intro x
                        (show g (f x) = z,
                         from eq.trans (congr_arg g hx) hy)))

-- 8ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
λ z, exists.elim (hg z)
       (λ y hy, exists.elim (hf y)
                  (λ x hx, exists.intro x
                             (show g (f x) = z,
                              from eq.trans (congr_arg g hx) hy)))

-- 9ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
-- by library_search
surjective.comp hg hf
