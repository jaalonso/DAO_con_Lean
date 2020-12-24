-- Introducción del cuantificador universal: La función cuadrado es par
-- ====================================================================

import tactic
import data.real.basic

-- ----------------------------------------------------
-- Ejercicio 1. Demostrar que
--    ∀ x : ℝ, (-x)^2 = x^2
-- ----------------------------------------------------

-- 1ª demostración
example :
  ∀ x : ℝ, (-x)^2 = x^2 :=
begin
  intro a,
  -- by library_search,
  exact neg_square a,
end

-- 2ª demostración
example :
  ∀ x : ℝ, (-x)^2 = x^2 :=
neg_square

-- 3ª demostración
example :
  ∀ x : ℝ, (-x)^2 = x^2 :=
begin
  intro a,
  -- by hint,
  ring,
end

-- 4ª demostración
example :
  ∀ x : ℝ, (-x)^2 = x^2 :=
begin
  intro a,
  norm_num,
end

-- 5ª demostración
example :
  ∀ x : ℝ, (-x)^2 = x^2 :=
by norm_num

-- 6ª demostración
example :
  ∀ x : ℝ, (-x)^2 = x^2 :=
begin
  intro a,
  finish,
end

-- 7ª demostración
example :
  ∀ x : ℝ, (-x)^2 = x^2 :=
by finish

-- 8ª demostración
example :
  ∀ x : ℝ, (-x)^2 = x^2 :=
begin
  intro a,
  simp,
end

-- 9ª demostración
example :
  ∀ x : ℝ, (-x)^2 = x^2 :=
by simp
