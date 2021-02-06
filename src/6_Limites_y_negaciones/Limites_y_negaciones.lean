import data.real.basic

section

-- Notaciones.
variables  (u : ℕ → ℝ)
variables  (f : ℝ → ℝ)
variables  (x₀ l : ℝ)

-- ----------------------------------------------------
-- Ejercicio. Definir la notación |x| para el valor
-- absoluto de x.
-- ----------------------------------------------------

notation `|`x`|` := abs x

-- ----------------------------------------------------
-- Ejercicio. Definir la función
--    limite : (ℕ → ℝ) → ℝ → Prop
-- tal que (limite u c) expresa que c es el límite de
-- la sucesión u.
-- ----------------------------------------------------

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    ¬ limite u l ↔ ∃ ε > 0, ∀ N, ∃ n ≥ N, |u n - l| > ε
-- ----------------------------------------------------------------------

example :
  ¬ limite u l ↔ ∃ ε > 0, ∀ N, ∃ n ≥ N, |u n - l| > ε :=
begin
  unfold limite,
  push_neg,
  simp,
end

-- ----------------------------------------------------
-- Ejercicio. Definir la función
--    continua : (ℝ → ℝ) → ℝ → Prop
-- tal que (continua f x₀) se verifica si f es continua
-- en x₀.
-- ----------------------------------------------------

def continua : (ℝ → ℝ) → ℝ → Prop :=
λ f x₀, ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ →  |f x - f x₀| ≤ ε

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--   ¬ (continua f x₀) ↔
--   ∃ ε > 0, ∀ δ > 0, ∃ x, |x - x₀| ≤ δ ∧ |f x - f x₀| > ε
-- ----------------------------------------------------------------------

example :
  ¬ (continua f x₀) ↔
  ∃ ε > 0, ∀ δ > 0, ∃ x, |x - x₀| ≤ δ ∧ |f x - f x₀| > ε :=
begin
  unfold continua,
  push_neg,
  simp,
end

-- ----------------------------------------------------
-- Ejercicio. Definir la función
--    uniformemente_continua : (ℝ → ℝ) → Prop
-- tal que (uniformemente_continua f) se verifica si f
-- es uniformemente continua.
-- ----------------------------------------------------

def uniformemente_continua : (ℝ → ℝ) → Prop :=
λ f, ∀ ε > 0, ∃ δ > 0, ∀ x x', |x' - x| ≤ δ →  |f x' - f x| ≤ ε

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    ¬ (uniformemente_continua f) ↔
--    ∃ ε > 0, ∀ δ > 0, ∃ x x', |x' - x| ≤ δ ∧ |f x' - f x| > ε :=
-- ----------------------------------------------------------------------

example :
  ¬ (uniformemente_continua f) ↔
  ∃ ε > 0, ∀ δ > 0, ∃ x x', |x' - x| ≤ δ ∧ |f x' - f x| > ε :=
begin
  unfold uniformemente_continua,
  push_neg,
  simp,
end

-- ----------------------------------------------------
-- Ejercicio. Definir la función
--    secuencialmente_continua : (ℝ → ℝ) → Prop
-- tal que (secuencialmente_continua f x₀) se verifica
-- si f es secuencialmente continua en x₀.
-- ----------------------------------------------------

def secuencialmente_continua : (ℝ → ℝ) → ℝ → Prop :=
λ f x₀, ∀ u : ℕ → ℝ, (∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - x₀| ≤ ε) →
                     (∀ ε > 0, ∃ N, ∀ n ≥ N, |(f ∘ u) n - f x₀| ≤ ε)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    ¬ secuencialmente_continua f x₀  ↔
--    ∃ u : ℕ → ℝ,
--      (∀ δ > 0, ∃ N, ∀ n ≥ N, |u n - x₀| ≤ δ) ∧
--      (∃ ε > 0,  ∀ N, ∃ n ≥ N, |f (u n) - f x₀| > ε)
-- ----------------------------------------------------------------------

example :
  ¬ secuencialmente_continua f x₀  ↔
  ∃ u : ℕ → ℝ,
    (∀ δ > 0, ∃ N, ∀ n ≥ N, |u n - x₀| ≤ δ) ∧
    (∃ ε > 0,  ∀ N, ∃ n ≥ N, |f (u n) - f x₀| > ε) :=
begin
  unfold secuencialmente_continua,
  push_neg,
  simp,
end
end

-- ----------------------------------------------------
-- Ejercicio. Definir la función
-- ----------------------------------------------------

def tiende_a_infinito : (ℕ → ℝ) → Prop :=
λ u, ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    tiende_a_infinito u → ∀ l, ¬ limite u l
-- ----------------------------------------------------------------------

example
  {u : ℕ → ℝ}
  : tiende_a_infinito u → ∀ l, ¬ limite u l :=
begin
  intros h l hl,
  cases hl 1 (by linarith) with N hN,
  cases h (l+2) with N' hN',
  let N₀ := max N N',
  specialize hN N₀ (le_max_left _ _),
  specialize hN' N₀ (le_max_right _ _),
  rw abs_le at hN,
  linarith,
end

-- ----------------------------------------------------
-- Ejercicio. Definir la función
--    no_decreciente : (ℕ → ℝ) → Prop
-- tal que (no_dreciente u) expresa que la sucesión u
-- es no decreciente.
-- ----------------------------------------------------

def no_decreciente : (ℕ → ℝ) → Prop :=
λ u, ∀ n m, n ≤ m → u n ≤ u m

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si u es una sucesión no decreciente y su
-- límite es l, entonces
--    ∀ n, u n ≤ l
-- ----------------------------------------------------------------------

example
  (u : ℕ → ℝ)
  (l : ℝ)
  (h : limite u l)
  (h' : no_decreciente u)
  : ∀ n, u n ≤ l :=
begin
  intro n,
  by_contradiction H,
  push_neg at H,
  cases h ((u n - l)/2) (by linarith) with N hN,
  specialize hN (max n N) (le_max_right _ _),
  specialize h' n (max n N) (le_max_left _ _),
  rw abs_le at hN,
  linarith,
end

-- ----------------------------------------------------
-- Ejercicio. Definir la función
--    cota_superior : set ℝ → ℝ → Prop
-- tal que (cota_superior A x) expresa que x es una
-- cota superior de A.
-- ----------------------------------------------------

def cota_superior : set ℝ → ℝ → Prop :=
λ A x, ∀ a ∈ A, a ≤ x

-- ----------------------------------------------------
-- Ejercicio. Definir la función
--    es_supremo : set ℝ → ℝ → Prop
-- tal que (es_supremos A x) expresa que x es el
-- supremo de A.
-- ----------------------------------------------------

def es_supremo : set ℝ → ℝ → Prop :=
λ A x, cota_superior A x ∧ ∀ y, cota_superior A y → x ≤ y

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si x es el supremo de A, entonces
--    ∀ y, y < x → ∃ a ∈ A, y < a
-- ----------------------------------------------------------------------

example
  {A : set ℝ}
  {x : ℝ}
  (hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intro y,
  contrapose!,
  exact hx.right y,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (∀ ε > 0, y ≤ x + ε) →  y ≤ x
-- ----------------------------------------------------------------------

lemma le_of_le_add_all'
  {x y : ℝ} :
  (∀ ε > 0, y ≤ x + ε) →  y ≤ x :=
begin
  contrapose!,
  intro h,
  use (y-x)/2,
  split ; linarith,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si x es el límite de u e y es una cota
-- superior de u, entonces x ≤ y.
-- ----------------------------------------------------------------------

example
  {x y : ℝ}
  {u : ℕ → ℝ}
  (hu : limite u x)
  (h : ∀ n, u n ≤ y)
  : x ≤ y :=
begin
  apply le_of_le_add_all',
  intros ε hε,
  cases hu ε hε with N hN,
  specialize hN N (by linarith),
  rw abs_le at hN,
  linarith [h N],
end
