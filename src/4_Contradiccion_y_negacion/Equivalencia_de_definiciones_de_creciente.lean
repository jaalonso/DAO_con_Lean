-- Equivalencia de definiciones de creciente
-- =========================================

import data.real.basic
variable (f : ℝ → ℝ)

example :
  (∀ x y, x < y → f x < f y) ↔ (∀ x y, (x ≤ y ↔ f x ≤ f y)) :=
begin
  split,
  { intros hf x y,
    split,
    { intros hxy,
      cases eq_or_lt_of_le hxy with hxy hxy,
      { rw hxy },
      { linarith [hf x y hxy]} },
    { contrapose!,
      apply hf } },
  { intros hf x y,
    contrapose!,
    intro h,
    rwa hf, }
end
