-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones 
-- 1. Importar la teoría de los números reales.
-- 2. Importar la librería con la táctica de sugerencias.
-- 3. Declarar la teoría como no cumputable.
-- 4. Usar la lógica clásica.
-- ----------------------------------------------------------------------

import data.real.basic -- 1
import tactic.suggest  -- 2
noncomputable theory   -- 3
open_locale classical  -- 4

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    up_bounds : set ℝ → set ℝ
-- tal que (up_bounds A) es el conjunto de las cotas superiores de A.
-- ----------------------------------------------------------------------

def up_bounds (A : set ℝ) : set ℝ := 
  { x : ℝ | ∀ a ∈ A, a ≤ x}

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    is_max : ℝ → set ℝ → Prop
-- tal que (is_max a A) afirma que a es un máximo de A.
-- ----------------------------------------------------------------------

def is_max (a : ℝ) (A : set ℝ) : Prop := 
  a ∈ A ∧ a ∈ up_bounds A

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la notación infija de is_max de forma que
-- se pueda escribir `a is_a_max_of A` en lugar de `is_max a A`.
-- ----------------------------------------------------------------------

infix ` is_a_max_of `:55 := is_max

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar la unicidad del máximo; es decir, un conjunto
-- no puede poseer más de un máximo.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

lemma unique_max 
  (A : set ℝ) 
  (x y : ℝ) 
  (hx : x is_a_max_of A) 
  (hy : y is_a_max_of A) 
  : x = y :=
begin
  cases hx with x_in x_up,
  cases hy with y_in y_up,
  specialize x_up y y_in,
  specialize y_up x x_in,
  linarith,
end

-- Comentarios:
-- 1. La táctica (cases h with h1 h2) cuando h es una conjunción aplica
--    la eliminación de la conjunción; es decir si (h : A ∧ B) la cambia
--    por (h1 : A) y (h2 : B). 
-- 2. La táctica (specialize h y) cuando h es del tipo (∀ x : α, P x)
--    aplica la eliminación del cuantificador universal; es decir
--    sustituye h por (y : α) y (h : P y). 
-- 3. La táctica (specialize h y h1) cuando h es del tipo 
--    (∀ x : α, P x → Q x) y h1 es del tipo (P y) aplica la eliminación
--    del cuantificador universal y de la implicación; es decir
--    sustituye h por (y : α) y (h : Q y).  
-- 4. La táctica linarith intenta demostrar la conclusión mediante la
--    aritmética lineal.

-- 2ª demostración
-- ===============

example 
  (A : set ℝ) 
  (x y : ℝ) 
  (hx : x is_a_max_of A) 
  (hy : y is_a_max_of A) 
  : x = y :=
begin
  have : x ≤ y, from hy.2 x hx.1,
  have : y ≤ x, from hx.2 y hy.1,
  linarith,
end

-- Comentarios: 1. Si h es una conjunción, entonces h.1 y h.2 son sus
-- componentes; es decir, si h es (A ∧ B) entonces h.1 es A y h.2 es B.

-- 3ª demostración
-- ===============

example 
  (A : set ℝ) 
  (x y : ℝ) 
  (hx : x is_a_max_of A) 
  (hy : y is_a_max_of A) 
  : x = y :=
begin
  apply le_antisymm,
  { have h1 : x ∈ A := hx.1,
    have h2 : ∀ x ∈ A, x ≤ y := hy.2,
    show x ≤ y, from
      h2 x h1 },
  { have h3 : y ∈ A := hy.1,
    have h4 : ∀ y ∈ A, y ≤ x := hx.2,
    show y ≤ x, from
      h4 y h3 },
end

-- 4ª demostración
-- ===============

example 
  (A : set ℝ) 
  (x y : ℝ) 
  (hx : x is_a_max_of A) 
  (hy : y is_a_max_of A) 
  : x = y :=
le_antisymm
  ( have h1 : x ∈ A := hx.1,
    have h2 : ∀ x ∈ A, x ≤ y := hy.2,
    show x ≤ y, from
      h2 x h1 )
  ( have h3 : y ∈ A := hy.1,
    have h4 : ∀ y ∈ A, y ≤ x := hx.2,
    show y ≤ x, from
      h4 y h3 )

-- 5ª demostración
-- ===============

example 
  (A : set ℝ) 
  (x y : ℝ) 
  (hx : x is_a_max_of A) 
  (hy : y is_a_max_of A) 
  : x = y :=
le_antisymm (hy.2 x hx.1) (hx.2 y hy.1)

-- Comentario: Se ha usado el lema
-- + le_antisymm : a ≤ b → b ≤ a → a = b 

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    low_bounds : set ℝ → set ℝ
-- tal que (low_bounds A) es el conjunto de las cotas inferiores de A.
-- ----------------------------------------------------------------------

def low_bounds (A : set ℝ) := 
  { x : ℝ | ∀ a ∈ A, x ≤ a}

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    is_inf : ℝ → set ℝ → Prop
-- tal que (is_inf x A) afirma que x es el ínfimo de A.
-- ----------------------------------------------------------------------

def is_inf (x : ℝ) (A : set ℝ) : Prop := 
  x is_a_max_of (low_bounds A)

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la notación infija de is_inf de forma que
-- se pueda escribir `a is_an_inf A` en lugar de `is_inf a A`.
-- ----------------------------------------------------------------------

infix ` is_an_inf_of `:55 := is_inf

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si y es mayor que el ínfimo de A, entonces
-- existe algún elemento a en A tal que a < y.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

lemma inf_lt 
  {A : set ℝ} 
  {x : ℝ} 
  (hx : x is_an_inf_of A) 
  : ∀ y, x < y → ∃ a ∈ A, a < y :=
begin
  intro y,
  contrapose,
  push_neg,
  intro h,
  exact hx.2 y h
end

-- Comentarios:
-- 1. La táctica (intro y) cuando la conclusión es una forma universal
--    aplica la regla de introducción del cuantificador universal; es
--    decir, si la conclusión es (∀ x : α, P x) añade la hipótesis (y : α)   
--    y cambia la conclusión por (P y).
-- 2. La táctica contrapose cuando la conclusión es una implicación, la
--    cambia por su contrapositiva; es decir, si la conclusión es (A → B)
--    la cambia por (¬B → ¬ A).
-- 3. La táctica push_neg interioriza las negaciones.
-- 4. La táctica (intro h) cuando la conclusión es una implicación
--    aplica la regla de introducción del condicional; es decir, si la
--    conclusión es (A → B) entonces añade la hipótesis (h : A) y cambia la
--    conclusión por B.

-- 2ª demostración
-- ===============

example
  {A : set ℝ} 
  {x : ℝ} 
  (hx : x is_an_inf_of A) 
  : ∀ y, x < y → ∃ a ∈ A, a < y :=
begin
  intro y,
  contrapose!,
  intro h,
  exact hx.2 y h
end

-- Comentarios:
-- 1. la táctica contrapose aplica sucesivamente las tácticas contrapose
-- y push_neg.

------------------------------------------------------------------------
-- § Desigualdades entre límites de sucesiones                        --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si (y ≤ x + ε) para todo número positivo ε,
-- entonces y ≤ x. 
-- ----------------------------------------------------------------------

lemma le_of_le_add_eps 
  {x y : ℝ} 
  : (∀ ε > 0, y ≤ x + ε) →  y ≤ x :=
begin
  -- Let's prove the contrapositive, asking Lean to push negations right away.
  contrapose!,
  -- Assume `h : x < y`.
  intro h,
  -- We need to find `ε` such that `ε` is positive and `x + ε < y`.
  -- Let's use `(y-x)/2`
  use ((y-x)/2),
  -- we now have two properties to prove. Let's do both in turn, using `linarith`
  split,
  linarith,
  linarith,
end

/-
Note how `linarith` was used for both sub-goals at the end of the above proof.
We could have shortened that using the semi-colon combinator instead of comma,
writing `split ; linarith`.

Next we will study a compressed version of that proof:
-/

example {x y : ℝ} : (∀ ε > 0, y ≤ x + ε) →  y ≤ x :=
begin
  contrapose!,
  exact assume h, ⟨(y-x)/2, by linarith, by linarith⟩,
end

/-
The angle brackets `⟨` and `⟩` introduce compound data or proofs. A proof
of a `∃ z, P z` statemement is composed of a witness `z₀` and a proof `h` of
`P z₀`. The compound is denoted by `⟨z₀, h⟩`. In the example above, the predicate is
itself compound, it is a conjunction `P z ∧ Q z`. So the proof term should read
`⟨z₀, ⟨h₁, h₂⟩⟩` where `h₁` (resp. `h₂`) is a proof of `P z₀` (resp. `Q z₀`).
But these so-called "anonymous constructor" brackets are right-associative, so we can
get rid of the nested brackets.

The keyword `by` introduces tactic mode inside term mode, it is a shorter version
of the `begin`/`end` pair, which is more convenient for single tactic blocks.
In this example, `begin` enters tactic mode, `exact` leaves it, `by` re-enters it.

Going all the way to a proof term would make the proof much longer, because we
crucially use automation with `contrapose!` and `linarith`. We can still get a one-line
proof using curly braces to gather several tactic invocations, and the `by` abbreviation
instead of `begin`/`end`:
-/

example {x y : ℝ} : (∀ ε > 0, y ≤ x + ε) →  y ≤ x :=
by { contrapose!, exact assume h, ⟨(y-x)/2, by linarith, by linarith⟩ }

/-
One could argue that the above proof is a bit too terse, and we are relying too much
on linarith. Let's have more `linarith` calls for smaller steps. For the sake
of (tiny) variation, we will also assume the premise and argue by contradiction
instead of contraposing.
-/

example {x y : ℝ} : (∀ ε > 0, y ≤ x + ε) →  y ≤ x :=
begin
  intro h,
  -- Assume the conclusion is false, and call this assumption H.
  by_contradiction H,
  push_neg at H,
  -- Now let's compute.
  have key := calc
  -- Each line must end with a colon followed by a proof term
  -- We want to specialize our assumption `h` to `ε = (y-x)/2` but this is long to
  -- type, so let's put a hole `_` that Lean will fill in by comparing the
  -- statement we want to prove and our proof term with a hole. As usual,
  -- positivity of `(y-x)/2` is proved by `linarith`
    y   ≤ x + (y-x)/2 : h _ (by linarith)
    ... = x/2 + y/2   : by ring
    ... < y           : by linarith,
  -- our key now says `y < y` (notice how the sequence `≤`, `=`, `<` was correctly
  -- merged into a `<`). Let `linarith` find the desired contradiction now.
  linarith,
  -- alternatively, we could have provided the proof term
  -- `exact lt_irrefl y key`
end

/-
Now we are ready for some analysis. Let's set up notation for absolute value
-/

local notation `|`x`|` := abs x

/-
And let's define convergence of sequences of real numbers (of course there is
a much more general definition in mathlib).
-/

/-- The sequence `u` tends to `l` -/
def limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-
In the above definition, `u n` denotes the n-th term of the sequence. We can
add parentheses to get `u(n)` but we try to avoid parentheses because they pile up
very quickly
-/

-- If y ≤ u n for all n and u n goes to x then y ≤ x
lemma le_lim {x y : ℝ} {u : ℕ → ℝ} (hu : limit u x) (ineq : ∀ n, y ≤ u n) : y ≤ x :=
begin
  -- Let's apply our previous lemma
  apply le_of_le_add_eps,
  -- We need to prove y ≤ x + ε for all positive ε.
  -- Let ε be any positive real
  intros ε ε_pos,
  -- we now specialize our limit assumption to this `ε`, and immediately
  -- fix a `N` as promised by the definition.
  cases hu ε ε_pos with N HN,
  -- Now we only need to compute until reaching the conclusion
  calc
  y ≤ u N             : ineq N
  ... = x + (u N - x) : by linarith
    -- We'll need `add_le_add` which says `a ≤ b` and `c ≤ d` implies `a + c ≤ b + d`
    -- We need a lemma saying `z ≤ |z|`. Because we don't know the name of this lemma,
    -- let's use `library_search`. Because searching thourgh the library is slow,
    -- Lean will write what it found in the Lean message window when cursor is on
    -- that line, so that we can replace it by the lemma. We see `le_max_left` which
    -- says `a ≤ max a b`. Actually there is a more specific lemma `le_abs_self`
  ... ≤ x + |u N - x| : add_le_add (by linarith) (by library_search)
  ... ≤ x + ε         : add_le_add (by linarith) (HN N (by linarith)),
end

/-
The next lemma has been extracted from the main proof in order to discuss numbers.
In ordinary maths, we know that ℕ is *not* contained in `ℝ`, whatever the
construction of real numbers that we use. For instance a natural number is not
an equivalence class of Cauchy sequences. But it's very easy to
pretend otherwise. Formal maths requires slightly more care. In the statement below,
the "type ascription" `(n + 1 : ℝ)` forces Lean to convert the natural number
`n+1` into a real number.  The "inclusion" map will be displayed in tactic state
as `↑`. There are various lemmas asserting this map is compatible with addition and
monotone, but we don't want to bother writing their names. The `norm_cast`
tactic is designed to wisely apply those lemmas for us.
-/

lemma inv_succ_pos : ∀ n : ℕ, 1/(n+1 : ℝ) > 0 :=
begin
  -- Let `n` be any integer
  intro n,
  -- Since we don't know the name of the relevant lemma, asserting that the inverse of
  -- a positive number is positive, let's state that is suffices
  -- to prove that `n+1`, seen as a real number, is positive, and ask `library_search`
  suffices : (n + 1 : ℝ) > 0,
  { library_search },
  -- Now we want to reduce to a statement about natural numbers, not real numbers
  -- coming from natural numbers.
  norm_cast,
  -- and then get the usual help from `linarith`
  linarith,
end

/-
That was a pretty long proof for an obvious fact. And stating it as a lemma feels
stupid, so let's find a way to write it on one line in case we want to include it
in some other proof without stating a lemma. First the `library_search` call
above displays the name of the relevant lemma: `one_div_pos_of_pos`. We can also
replace the `linarith` call on the last line by `library_search` to learn the name
of the lemma `nat.succ_pos` asserting that the successor of a natural number is
positive. There is also a variant on `norm_cast` that combines it with `exact`.
The term mode analogue of `intro` is `λ`. We get down to:
-/

example : ∀ n : ℕ, 1/(n+1 : ℝ) > 0 :=
λ n, one_div_pos_of_pos (by exact_mod_cast nat.succ_pos n)

/-
The next proof uses mostly known things, so we will commment only new aspects.
-/

lemma limit_inv_succ : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε :=
begin
  intros ε ε_pos,
  suffices : ∃ N : ℕ, 1/ε ≤ N,
  { -- Because we didn't provide a name for the above statement, Lean called it `this`.
    -- Let's fix an `N` that works.
    cases this with N HN,
    use N,
    intros n Hn,
    -- Now we want to rewrite the goal using lemmas
    -- `div_le_iff' : 0 < b →  (a / b ≤ c ↔ a ≤ b * c)`
    -- `div_le_iff : 0 < b →  (a / b ≤ c ↔ a ≤ c * b)`
    -- the second one will be rewritten from right to left, as indicated by `←`.
    -- Lean will create a side goal for the required positivity assumption that
    -- we don't provide for `div_le_iff'`.
    rw [div_le_iff', ← div_le_iff ε_pos],
    -- We want to replace assumption `Hn` by its real counter-part so that
    -- linarith can find what it needs.
    replace Hn : (N : ℝ) ≤ n, exact_mod_cast Hn,
    linarith,
    -- we are still left with the positivity assumption, but already discussed
    -- how to prove it in the preceding lemma
    exact_mod_cast nat.succ_pos n },
  -- Now we need to prove that sufficient statement.
  -- We want to use that `ℝ` is archimedean. So we start typing
  -- `exact archimedean_` and hit Ctrl-space to see what completion Lean proposes
  -- the lemma `archimedean_iff_nat_le` sounds promising. We select the left to
  -- right implication using `.1`. This a generic lemma for fields equiped with
  -- a linear (ie total) order. We need to provide a proof that `ℝ` is indeed
  -- archimedean. This is done using the `apply_instance` tactic that will be
  -- covered elsewhere.
  exact archimedean_iff_nat_le.1 (by apply_instance) (1/ε),
end

/-
We can now put all pieces together, with almost no new things to explain.
-/

lemma inf_seq (A : set ℝ) (x : ℝ) :
  (x is_an_inf_of A) ↔ (x ∈ low_bounds A ∧ ∃ u : ℕ → ℝ, limit u x ∧ ∀ n, u n ∈ A ) :=
begin
  split,
  { intro h,
    split,
    { exact h.1 },
    -- On the next line, we don't need to tell Lean to treat `n+1` as a real number because
    -- we add `x` to it, so Lean knows there is only one way to make sense of this expression.
    have key : ∀ n : ℕ, ∃ a ∈ A, a < x + 1/(n+1),
    { intro n,
      -- we can use the lemma we proved above
      apply inf_lt h,
      -- and another one we proved!
      have : 0 < 1/(n+1 : ℝ), from inv_succ_pos n,
      linarith },
    -- Now we need to use axiom of (countable) choice
    choose u hu using key,
    use u,
    split,
    { intros ε ε_pos,
      -- again we use a lemma we proved, specializing it to our fixed `ε`, and fixing a `N`
      cases limit_inv_succ ε ε_pos with N H,
      use N,
      intros n hn,
      have : x ≤ u n, from h.1 _ (hu n).1,
      have := calc
        u n < x + 1/(n + 1) : (hu n).2
        ... ≤ x + ε         : add_le_add (le_refl x) (H n hn),
      rw abs_of_nonneg ; linarith },
    { intro n,
      exact (hu n).1 } },
  { intro h,
    -- Assumption `h` is made of nested compound statements. We can use the
    -- recursive version of `cases` to unpack it in one go.
    rcases h with ⟨x_min, u, lim, huA⟩,
    split,
    exact x_min,
    intros y y_mino,
    apply le_lim lim,
    intro n,
    exact y_mino (u n) (huA n) },
end


