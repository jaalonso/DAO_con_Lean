-- CS menor o igual que cero
-- =========================

import data.real.basic
variable (x : ℝ)

-- 1ª demostración
example :
  (∀ ε > 0, x ≤ ε) → x ≤ 0 :=
begin
  contrapose,
  push_neg,
  intro h,
  use x/2,
  split ; linarith,
end

-- 2ª demostración
example :
  (∀ ε > 0, x ≤ ε) → x ≤ 0 :=
begin
  contrapose!,
  intro h,
  use x/2,
  split ; linarith,
end
