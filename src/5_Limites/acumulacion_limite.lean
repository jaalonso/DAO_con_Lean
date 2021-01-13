-- El punto de acumulación de las convergentes es su límite
-- ========================================================

import data.real.basic

variable  {u : ℕ → ℝ}
variables {a b: ℝ}
variables (x y : ℝ)
variable  {φ : ℕ → ℕ}

-- ----------------------------------------------------
-- Nota. Usaremos los siguientes conceptos estudiados
-- anteriormente.
-- ----------------------------------------------------

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε

lemma cero_de_abs_mn_todos
  (h : ∀ ε > 0, |x| ≤ ε)
  : x = 0 :=
abs_eq_zero.mp
  (eq_of_le_of_forall_le_of_dense (abs_nonneg x) h)

lemma ig_de_abs_sub_mne_todos
  (h : ∀ ε > 0, |x - y| ≤ ε)
  : x = y :=
sub_eq_zero.mp (cero_de_abs_mn_todos (x - y) h)

lemma unicidad_limite
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
begin
  apply ig_de_abs_sub_mne_todos,
  intros ε hε,
  cases ha (ε/2) (by linarith) with Na hNa,
  cases hb (ε/2) (by linarith) with Nb hNb,
  let N := max Na Nb,
  specialize hNa N (by finish),
  specialize hNb N (by finish),
  calc |a - b|
       = |(a - u N) + (u N - b)| : by ring
   ... ≤ |a - u N| + |u N - b|   : by apply abs_add
   ... = |u N - a| + |u N - b|   : by rw abs_sub
   ... ≤ ε                       : by linarith [hNa, hNb]
end

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

def punto_acumulacion : (ℕ → ℝ) → ℝ → Prop
| u a := ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

lemma limite_subsucesion
  (h : limite u a)
  (hφ : extraccion φ)
  : limite (u ∘ φ) a :=
assume ε,
assume hε : ε > 0,
exists.elim (h ε hε)
 ( assume N,
   assume hN : ∀ n, n ≥ N → |u n - a| ≤ ε,
   have h1 : ∀n, n ≥ N → |(u ∘ φ) n - a| ≤ ε,
     { assume n,
       assume hn : n ≥ N,
       have h2 : N ≤ φ n, from
         calc N ≤ n   : hn
           ... ≤ φ n : id_mne_extraccion hφ n,
       show |(u ∘ φ) n - a| ≤ ε,
         from hN (φ n) h2,
     },
   show ∃ N, ∀n, n ≥ N → |(u ∘ φ) n - a| ≤ ε,
     from exists.intro N h1)

-- ----------------------------------------------------
-- Ejercicio. Demostrar que si a es un punto de
-- acumulación de una sucesión de límite b, entonces a
-- y b son iguales.
-- ----------------------------------------------------

-- 1ª demostración
example
  (ha : punto_acumulacion u a)
  (hb : limite u b)
  : a = b :=
begin
  -- unfold punto_acumulacion at ha,
  rcases ha with ⟨φ, hφ₁, hφ₂⟩,
  have hφ₃ : limite (u ∘ φ) b,
    from limite_subsucesion hb hφ₁,
  exact unicidad_limite hφ₂ hφ₃,
end

-- 2ª demostración
example
  (ha : punto_acumulacion u a)
  (hb : limite u b)
  : a = b :=
begin
  rcases ha with ⟨φ, hφ₁, hφ₂⟩,
  exact unicidad_limite hφ₂ (limite_subsucesion hb hφ₁),
end

-- 3ª demostración
example
  (ha : punto_acumulacion u a)
  (hb : limite u b)
  : a = b :=
exists.elim ha
  (λ φ hφ, unicidad_limite hφ.2 (limite_subsucesion hb hφ.1))

-- 4ª demostración
example
  (ha : punto_acumulacion u a)
  (hb : limite u b)
  : a = b :=
exists.elim ha
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    have hφ' : limite (u ∘ φ) b,
      from limite_subsucesion hb hφ.1,
    show a = b,
      from unicidad_limite hφ.2 hφ')
