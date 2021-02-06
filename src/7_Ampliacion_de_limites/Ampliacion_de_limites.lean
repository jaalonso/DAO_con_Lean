import data.real.basic
import topology.metric_space.basic
import analysis.specific_limits
import topology.sequences
import order.filter.at_top_bot
import tactic

variable {f : ℝ → ℝ}
variable {x₀ : ℝ}
variable {u : ℕ → ℝ}
variable {φ : ℕ → ℕ}

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
--    (∀ ε > 0, y ≤ x + ε) →  y ≤ x
-- ----------------------------------------------------------------------

lemma le_of_le_add_all
  {x y : ℝ}
  : (∀ ε > 0, y ≤ x + ε) →  y ≤ x :=
begin
  contrapose!,
  intro h,
  use (y-x)/2,
  split ; linarith,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si x es el límite de u y
--    ∃ N, ∀ n ≥ N, y ≤ u n
-- entonce y ≤ x.
-- ----------------------------------------------------------------------

lemma le_lim
  {x y : ℝ}
  {u : ℕ → ℝ}
  (hu : limite u x)
  (h : ∃ N, ∀ n ≥ N, y ≤ u n)
  : y ≤ x :=
begin
  apply le_of_le_add_all,
  intros ε hε,
  cases hu ε hε with N hN,
  cases h with N' hN',
  let N₀ := max N N',
  specialize hN N₀ (le_max_left N N'),
  specialize hN' N₀ (le_max_right N N'),
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
-- Ejercicio. Demostrar que si x es el supremo de A,
-- entonces
--    ∀ y, y < x → ∃ a ∈ A, y < a
-- ----------------------------------------------------------------------

lemma lt_sup
  {A : set ℝ}
  {x : ℝ} (
  hx : es_supremo A x)
  : ∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intro y,
  contrapose!,
  exact hx.right y,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    limite (λ n, x) x
-- ----------------------------------------------------------------------

lemma limit_const
  (x : ℝ)
  : limite (λ n, x) x :=
λ ε ε_pos, ⟨0, λ _ _, by simp [le_of_lt ε_pos]⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si x es el límite de u e y es una cota
-- superior de u, entonces x ≤ y.
-- ----------------------------------------------------------------------

lemma lim_le
  {x y : ℝ}
  {u : ℕ → ℝ}
  (hu : limite u x)
  (ineg : ∀ n, u n ≤ y)
  : x ≤ y :=
begin
  apply le_of_le_add_all,
  intros ε ε_pos,
  cases hu ε ε_pos with N hN,
  specialize hN N (by linarith),
  specialize ineg N,
  rw abs_le at hN,
  linarith,
end

-- ----------------------------------------------------
-- Ejercicio. Demostrar que si dos sucesiones tienen
-- el mismo límite, entonces las sucesiones que están
-- comprendidas entre éstas también tienen el mismo
-- límite.
-- ----------------------------------------------------

-- Nota. En la demostración se usará el siguiente lema:
lemma max_ge_iff
  {p q r : ℕ}
  : r ≥ max p q ↔ r ≥ p ∧ r ≥ q :=
max_le_iff

lemma emparedado
  {u v w : ℕ → ℝ}
  {a : ℝ}
  (hu : limite u a)
  (hw : limite w a)
  (h : ∀ n, u n ≤ v n)
  (h' : ∀ n, v n ≤ w n)
  : limite v a :=
begin
  intros ε hε,
  cases hu ε hε with N hN, clear hu,
  cases hw ε hε with N' hN', clear hw hε,
  use max N N',
  intros n hn,
  rw max_ge_iff at hn,
  specialize hN n (by linarith),
  specialize hN' n (by linarith),
  specialize h n,
  specialize h' n,
  rw abs_le at *,
  split ; linarith,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε
-- ----------------------------------------------------------------------

lemma inv_succ_le_all :
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε :=
begin
  convert metric.tendsto_at_top.mp (tendsto_one_div_add_at_top_nhds_0_nat),
  apply propext,
  simp only [real.dist_eq, sub_zero],
  split,
    { intros h ε ε_pos,
      cases h (ε/2) (by linarith) with N hN,
      use N,
      intros n hn,
      rw abs_of_pos (nat.one_div_pos_of_nat : 1/(n+1 : ℝ) > 0),
      specialize hN n hn,
      linarith, },
  intros h ε ε_pos,
  cases h ε (by linarith) with N hN,
  use N,
  intros n hn,
  specialize hN n hn,
  rw abs_of_pos (@nat.one_div_pos_of_nat ℝ _ n) at hN,
  linarith,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    ∀ n, |u n - x| ≤ 1/(n+1) ⊢ limite u x
-- ----------------------------------------------------------------------

lemma limit_of_sub_le_inv_succ
  {u : ℕ → ℝ}
  {x : ℝ}
  (h : ∀ n, |u n - x| ≤ 1/(n+1))
  : limite u x :=
begin
  intros ε ε_pos,
  rcases inv_succ_le_all ε ε_pos with ⟨N, hN⟩,
  use N,
  intros n hn,
  specialize h n,
  specialize hN n hn,
  linarith,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que x es el límite de
--   x - 1/(n+1)) x
-- ----------------------------------------------------------------------

lemma limit_const_sub_inv_succ
  (x : ℝ)
  : limite (λ n, x - 1/(n+1)) x :=
begin
  refine limit_of_sub_le_inv_succ (λ n, _),
  rw [show x - 1 / (n + 1) - x = -(1/(n+1)), by ring, abs_neg,  abs_of_pos],
  linarith [@nat.one_div_pos_of_nat ℝ _ n]
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que son equivalentes
-- + es_supremo A x
-- + cota_superior A x ∧ ∃ u : ℕ → ℝ, limite u x ∧ ∀ n, u n ∈ A
-- ----------------------------------------------------------------------

lemma es_supremo_iff
  (A : set ℝ)
  (x : ℝ)
  : (es_supremo A x) ↔
    (cota_superior A x ∧ ∃ u : ℕ → ℝ, limite u x ∧ ∀ n, u n ∈ A ) :=
begin
  split,
  { intro h,
    split,
    { exact h.left, },
    { have : ∀ n : ℕ, ∃ a ∈ A, x - 1/(n+1) < a,
      { intros n,
        have : 1/(n+1 : ℝ) > 0,
          exact nat.one_div_pos_of_nat,
        exact lt_sup h _ (by linarith), },
      choose u hu using this,
      use u,
      split,
      { apply emparedado (limit_const_sub_inv_succ x) (limit_const x),
        { intros n,
          exact le_of_lt (hu n).2, },
        { intro n,
          exact h.1 _ (hu n).left, } },
      { intro n,
        exact (hu n).left }}},
  { rintro ⟨maj, u, limu, u_in⟩,
    split,
    { exact maj },
    { intros y ymaj,
      apply lim_le limu,
      intro n,
      apply ymaj,
      apply u_in }},
end

-- ----------------------------------------------------
-- Ejercicio. Definir la función
--    continua_en_punto : (ℝ → ℝ) → ℝ → Prop
-- tal que (continua_en_punto f x₀) expresa que f es
-- continua en x₀.
-- ----------------------------------------------------

def continua_en_punto : (ℝ → ℝ) → ℝ → Prop :=
λ f x₀, ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si el límite de f es x₀ y f es continua en
-- x₀, entonces el límite de (f ∘ u) es f(x₀).
-- ----------------------------------------------------------------------

lemma seq_continuous_of_continuous
  (hf : continua_en_punto f x₀)
  (hu : limite u x₀)
  : limite (f ∘ u) (f x₀) :=
begin
  intros ε ε_pos,
  rcases hf ε ε_pos with ⟨δ, δ_pos, hδ⟩,
  cases hu δ δ_pos with N hN,
  use N,
  intros n hn,
  apply hδ,
  exact hN n hn,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    ∀ u : ℕ → ℝ, limite u x₀ → limite (f ∘ u) (f x₀)
-- entonces f es continua en x₀.
-- ----------------------------------------------------------------------

example :
  (∀ u : ℕ → ℝ, limite u x₀ → limite (f ∘ u) (f x₀)) →
  continua_en_punto f x₀ :=
begin
  contrapose!,
  intro hf,
  unfold continua_en_punto at hf,
  push_neg at hf,
  cases hf with ε h,
  cases h with ε_pos hf,
  have H : ∀ n : ℕ, ∃ x, |x - x₀| ≤ 1/(n+1) ∧ ε < |f x - f x₀|,
    intro n,
    apply hf,
    exact nat.one_div_pos_of_nat,
  clear hf,
  choose u hu using H,
  use u,
  split,
    intros η η_pos,
    have fait : ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → 1 / (↑n + 1) ≤ η,
      exact inv_succ_le_all η η_pos,
    cases fait with N hN,
    use N,
    intros n hn,
    calc |u n - x₀| ≤ 1/(n+1) : (hu n).left
                ... ≤ η       : hN n hn,
  unfold limite,
  push_neg,
  use [ε, ε_pos],
  intro N,
  use N,
  split,
  linarith,
  exact (hu N).right,
end

-- ----------------------------------------------------
-- Ejercicio. Definir la función
-- ----------------------------------------------------

def tiende_a_infinito : (ℕ → ℝ) → Prop :=
λ u, ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A

-- ----------------------------------------------------
-- Ejercicio. Para extraer una sucesión se aplica una
-- función de extracción que conserva el orden; por
-- ejemplo, la subsucesión
--    uₒ, u₂, u₄, u₆, ...
-- se ha obtenido con la función de extracción φ tal
-- que φ(n) = 2*n.
--
-- Definir la función
--    extraccion : (ℕ → ℕ) → Prop
-- tal que (extraccion φ) expresa que φ es una función
-- de extracción
-- ----------------------------------------------------

def extraccion : (ℕ → ℕ) → Prop
| φ := ∀ n m, n < m → φ n < φ m

-- ----------------------------------------------------
-- Ejercicio. Demostrar que si φ es una función de
-- extracción, entonces
--    ∀ n, n ≤ φ n
-- ----------------------------------------------------

lemma id_mne_extraccion :
  extraccion φ → ∀ n, n ≤ φ n :=
begin
  intros h n,
  induction n with m HI,
  { linarith },
  { apply nat.succ_le_of_lt,
    linarith [h m (m+1) (by linarith)] },
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si u tiende a infinito y φ es una función de
-- extracción, entonces (u ∘ φ) tiende a infinito.
-- ----------------------------------------------------------------------

lemma subseq_tenstoinfinity
  (h : tiende_a_infinito u)
  (hφ : extraccion φ)
  : tiende_a_infinito (u ∘ φ) :=
begin
  intros A,
  cases h A with N hN,
  use N,
  intros n hn,
  apply hN,
  calc N ≤ n   : hn
     ... ≤ φ n : id_mne_extraccion hφ n,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si u tiende al infinito y
--    ∀ n, u n ≤ v n
-- entonces v tiende al infinito.
-- ----------------------------------------------------------------------

lemma squeeze_infinity
  {u v : ℕ → ℝ}
  (hu : tiende_a_infinito u)
  (huv : ∀ n, u n ≤ v n)
  : tiende_a_infinito v :=
begin
  intros A,
  cases hu A with N hN,
  use N,
  intros n hn,
  specialize hN n hn,
  specialize huv n,
  linarith,
end

open set

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la sucesión identidad tiende a infinito.
-- ----------------------------------------------------------------------

lemma limite_id : tiende_a_infinito (λ n, n) :=
begin
  intros A,
  cases exists_nat_gt A with N hN,
  use N,
  intros n hn,
  have : (n : ℝ) ≥ N,
    exact_mod_cast hn,
  linarith,
end

-- ----------------------------------------------------
-- Ejercicio. Definir la función
--    punto_acumulacion : (ℕ → ℝ) → ℝ → Prop
-- tal que (punto_acumulacion u a) expresa que a es un
-- punto de acumulación de u; es decir, que es el
-- límite de alguna subsucesión de u.
-- ----------------------------------------------------

def punto_acumulacion : (ℕ → ℝ) → ℝ → Prop
| u a := ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si es una sucesión en [a,b], entonces
-- existe algún c en [a,b] que es el punto de acumulación de u.
-- ----------------------------------------------------------------------

lemma bolzano_weierstrass
  {a b : ℝ}
  {u : ℕ → ℝ}
  (h : ∀ n, u n ∈ Icc a b)
  : ∃ c ∈ Icc a b, punto_acumulacion u c :=
begin
  rcases (compact_Icc : is_compact (Icc a b)).tendsto_subseq h with ⟨c, c_in, φ, hφ, lim⟩,
  use [c, c_in, φ, hφ],
  simp_rw [metric.tendsto_nhds, filter.eventually_at_top, real.dist_eq] at lim,
  intros ε ε_pos,
  rcases lim ε ε_pos with ⟨N, hN⟩,
  use N,
  intros n hn,
  exact le_of_lt (hN n hn)
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    tiende_a_infinito u → ∀ x, ¬ limite u x
-- ----------------------------------------------------------------------

lemma not_seq_limit_of_tendstoinfinity
  {u : ℕ → ℝ} :
  tiende_a_infinito u → ∀ x, ¬ limite u x :=
begin
  intros lim_infinie x lim_x,
  cases lim_x 1 (by linarith) with N hN,
  cases lim_infinie (x+2) with N' hN',
  let N₀ := max N N',
  specialize hN N₀ (le_max_left _ _),
  specialize hN' N₀ (le_max_right _ _),
  rw abs_le at hN,
  linarith,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es continua en [a,b], entonces existe
-- un M tal que, para todo x ∈ [a,b], f(x) ≤ M.
-- ----------------------------------------------------------------------

lemma bdd_above_segment
  {f : ℝ → ℝ}
  {a b : ℝ}
  (hf : ∀ x ∈ Icc a b, continua_en_punto f x)
  : ∃ M, ∀ x ∈ Icc a b, f x ≤ M :=
begin
  by_contradiction H,
  push_neg at H,
  have clef : ∀ n : ℕ, ∃ x, x ∈ Icc a b ∧ f x > n,
    intro n,
    apply H,
    clear H,
  choose u hu using clef,
  have lim_infinie : tiende_a_infinito (f ∘ u),
    apply squeeze_infinity (limite_id),
    intros n,
    specialize hu n,
    linarith,
  have bornes : ∀ n, u n ∈ Icc a b,
    intro n,
    exact (hu n).left,
  rcases bolzano_weierstrass bornes with ⟨c, c_dans, φ, φ_extr, lim⟩,
  have lim_infinie_extr : tiende_a_infinito (f ∘ (u ∘ φ)),
    exact subseq_tenstoinfinity lim_infinie φ_extr,
  have lim_extr : limite (f ∘ (u ∘ φ)) (f c),
    exact seq_continuous_of_continuous (hf c c_dans) lim,
  exact not_seq_limit_of_tendstoinfinity lim_infinie_extr (f c) lim_extr,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es continua en x₀, también lo es -f.
-- ----------------------------------------------------------------------

lemma continuous_opposite
  {f : ℝ → ℝ}
  {x₀ : ℝ}
  (h : continua_en_punto f x₀)
  : continua_en_punto (λ x, -f x) x₀ :=
begin
  intros ε ε_pos,
  cases h ε ε_pos with δ h,
  cases h with δ_pos h,
  use [δ, δ_pos],
  intros y hy,
  have :  -f y - -f x₀ = -(f y - f x₀), ring,
  rw [this, abs_neg],
  exact h y hy,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es continua en [a,b], entonces existe
-- un m en [a,b] tal que, para todo x de [a,b], m ≤ f(x).
-- ----------------------------------------------------------------------

lemma bdd_below_segment
  {f : ℝ → ℝ}
  {a b : ℝ}
  (hf : ∀ x ∈ Icc a b, continua_en_punto f x)
  : ∃ m, ∀ x ∈ Icc a b, m ≤ f x :=
begin
  have : ∃ M, ∀ x ∈ Icc a b, -f x ≤ M,
  { apply bdd_above_segment,
    intros x x_dans,
    exact continuous_opposite (hf x x_dans), },
  cases this with M hM,
  use -M,
  intros x x_dans,
  specialize hM x x_dans,
  linarith,
end

open real

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si A es un subconjunto no vacío de [a,b],
-- entonces existe un x en [a,b] que es el supremo de A.
-- ----------------------------------------------------------------------

lemma sup_segment
  {a b : ℝ}
  {A : set ℝ}
  (hnonvide : ∃ x, x ∈ A)
  (h : A ⊆ Icc a b)
  : ∃ x ∈ Icc a b, es_supremo A x :=
begin
  have b_maj : ∀ (y : ℝ), y ∈ A → y ≤ b,
    from λ y y_in, (h y_in).2,
  have Sup_maj : cota_superior A (Sup A),
  { intro x,
    apply real.le_Sup,
    use [b, b_maj] } ,
  refine ⟨Sup A, _, _⟩,
  { split,
    { cases hnonvide with x x_in,
      exact le_trans (h x_in).1 (Sup_maj _ x_in) },
    { apply Sup_le_ub A hnonvide b_maj } },
  { use Sup_maj,
    intros y y_in,
    rwa real.Sup_le _ hnonvide ⟨b, b_maj⟩ },
end

-- ----------------------------------------------------
-- Ejercicio. Demostrar que cada sucesión tiene como
-- máximo un límite.
-- ----------------------------------------------------

lemma unicidad_limite
  {a b : ℝ}
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
begin
  by_contradiction H,
  change a ≠ b at H,
  have h1 : |a - b| > 0,
    exact abs_pos.mpr (sub_ne_zero_of_ne H),
  cases ha (|a - b|/4) (by linarith) with N hN,
  cases hb (|a - b|/4) (by linarith) with N' hN',
  let N₀ := max N N',
  specialize hN N₀ (le_max_left _ _),
  specialize hN' N₀ (le_max_right _ _),
  have h2 : |a - b| < |a - b |,
    calc  |a - b| = |(a - u N₀) + (u N₀ - b)| : by ring
    ... ≤ |a - u N₀| + |u N₀ - b|             : by apply abs_add
    ... = |u N₀ - a| + |u N₀ - b|             : by rw abs_sub
    ... < |a - b|                             : by linarith,
  linarith,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si l es el límite de u y φ es una extracción,
-- entonces l es el límite de (u ∘ φ).
-- ----------------------------------------------------------------------

lemma subseq_tendsto_of_tendsto
  {l : ℝ}
  (h : limite u l)
  (hφ : extraccion φ)
  : limite (u ∘ φ) l :=
begin
  intros ε ε_pos,
  cases h ε ε_pos with N hN,
  use N,
  intros n hn,
  apply hN,
  calc N ≤ n   : hn
     ... ≤ φ n : id_mne_extraccion hφ n,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es continua en [a,b], existe un x₀ ∈ [a,b],
-- tal que, para todo x ∈ [a,b], f(x) ≤ f(x₀).
-- ----------------------------------------------------------------------

example
  {a b : ℝ}
  (hab : a ≤ b)
  (hf : ∀ x ∈ Icc a b, continua_en_punto f x)
  : ∃ x₀ ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f x₀ :=
begin
  cases bdd_below_segment hf with m hm,
  cases bdd_above_segment hf with M hM,
  let A := {y | ∃ x ∈ Icc a b, y = f x},
  obtain ⟨y₀, y_dans, y_sup⟩ : ∃ y₀ ∈ Icc m M, es_supremo A y₀,
  { apply sup_segment,
    { use [f a, a, by linarith, hab, by ring], },
    { rintros y ⟨x, x_in, rfl⟩,
      exact ⟨hm x x_in, hM x x_in⟩ } },
  rw es_supremo_iff at y_sup,
  rcases y_sup with ⟨y_maj, u, lim_u, u_dans⟩,
  choose v hv using u_dans,
  cases forall_and_distrib.mp hv with v_dans hufv,
  replace hufv : u = f ∘ v := funext hufv,
  rcases bolzano_weierstrass v_dans with ⟨x₀, x₀_in, φ, φ_extr, lim_vφ⟩,
  use [x₀, x₀_in],
  intros x x_dans,
  have lim : limite (f ∘ v ∘ φ) (f x₀),
  { apply seq_continuous_of_continuous,
    exact hf x₀ x₀_in,
    exact lim_vφ },
  have unique : f x₀ = y₀,
  { apply unicidad_limite lim,
    rw hufv at lim_u,
    exact subseq_tendsto_of_tendsto lim_u φ_extr },
  rw unique,
  apply y_maj,
  use [x, x_dans],
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si x ∈ [a,b] y x ≠ b, entonces x < b.
-- ----------------------------------------------------------------------

lemma stupid
  {a b x : ℝ}
  (h : x ∈ Icc a b)
  (h' : x ≠ b)
  : x < b :=
lt_of_le_of_ne h.right h'

-- ----------------------------------------------------
-- Ejercicio. Definir I como el intervalo [0,1].
-- ----------------------------------------------------

def I := (Icc 0 1 : set ℝ)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que x es el límite de
--    x + 1/(n+1)
-- ----------------------------------------------------------------------

lemma limit_const_add_inv_succ
  (x : ℝ)
  : limite (λ n, x + 1/(n+1)) x :=
limit_of_sub_le_inv_succ (λ n, by rw abs_of_pos ;
linarith [@nat.one_div_pos_of_nat ℝ _ n])

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es continua, f(0) < 0 y f(1) > 0,
-- entonces existe un x₀ ∈ I tal que f(x₀) = 0.
-- ----------------------------------------------------------------------

example
  (f : ℝ → ℝ)
  (hf : ∀ x, continua_en_punto f x)
  (h₀ : f 0 < 0)
  (h₁ : f 1 > 0)
  : ∃ x₀ ∈ I, f x₀ = 0 :=
begin
  let A := { x | x ∈ I ∧ f x < 0},
  have ex_x₀ : ∃ x₀ ∈ I, es_supremo A x₀,
  { apply sup_segment,
      use 0,
      split,
        split, linarith, linarith,
      exact h₀,
    intros x hx,
    exact hx.left },
  rcases ex_x₀ with ⟨x₀, x₀_in, x₀_sup⟩,
  use [x₀, x₀_in],
  have : f x₀ ≤ 0,
  { rw es_supremo_iff at x₀_sup,
    rcases x₀_sup with ⟨maj_x₀, u, lim_u, u_dans⟩,
    have : limite (f ∘ u) (f x₀),
      exact seq_continuous_of_continuous (hf x₀) lim_u,
    apply lim_le this,
    intros n,
    have : f (u n) < 0,
      exact (u_dans n).right,
    linarith  },
  have x₀_1: x₀ < 1,
  { apply stupid x₀_in,
    intro h,
    rw ← h at h₁,
    linarith  },
  have : f x₀ ≥ 0,
  { have in_I : ∃ N : ℕ, ∀ n ≥ N, x₀ + 1/(n+1) ∈ I,
    { have : ∃ N : ℕ, ∀ n≥ N, 1/(n+1 : ℝ) ≤ 1-x₀,
      { apply inv_succ_le_all,
        linarith, },
      cases this with N hN,
      use N,
      intros n hn,
      specialize hN n hn,
      have : 1/(n+1 : ℝ) > 0,
        exact nat.one_div_pos_of_nat,
      change 0 ≤ x₀ ∧ x₀ ≤ 1 at x₀_in,
      split ; linarith, },
    have not_in : ∀ n : ℕ, x₀ + 1/(n+1) ∉ A,
    -- By definition, x ∉ A means ¬ (x ∈ A).
    { intros n hn,
      cases x₀_sup with x₀_maj _,
      specialize x₀_maj _ hn,
      have : 1/(n+1 : ℝ) > 0,
        from nat.one_div_pos_of_nat,
      linarith, },
    dsimp [A] at not_in, -- This is useful to unfold a let
    push_neg at not_in,
    have lim : limite (λ n, f(x₀ + 1/(n+1))) (f x₀),
    { apply seq_continuous_of_continuous (hf x₀),
      apply limit_const_add_inv_succ },
    apply le_lim lim,
    cases in_I with N hN,
    use N,
    intros n hn,
    exact not_in n (hN n hn), },
  linarith,
end
