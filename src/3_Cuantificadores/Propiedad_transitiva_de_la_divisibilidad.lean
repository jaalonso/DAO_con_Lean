-- Propiedad transitiva de la divisibilidad
-- ========================================

import tactic

variables (a b c : ℤ)

-- #reduce a ∣ b
-- #print notation (∣)

-- ----------------------------------------------------
-- Ejercicio. Demostrar que si a divide a b y b divide
-- a c, entonces a divide a c.
-- ----------------------------------------------------

-- 1ª demostración
example
  (h₁ : a ∣ b)
  (h₂ : b ∣ c)
  : a ∣ c :=
begin
  -- unfold has_dvd.dvd at *,
  cases h₁ with k hk,
  cases h₂ with l hl,
  use k*l,
  rw hl,
  rw hk,
  rw mul_assoc,
end

-- 2ª demostración
example
  (h₁ : a ∣ b)
  (h₂ : b ∣ c)
  : a ∣ c :=
begin
  cases h₁ with k hk,
  cases h₂ with l hl,
  use k*l,
  calc c = b * l       : by rw hl
     ... = (a * k) * l : by rw hk
     ... = a * (k * l) : by rw mul_assoc,
end

-- 3ª demostración
example
  (h₁ : a ∣ b)
  (h₂ : b ∣ c)
  : a ∣ c :=
begin
  cases h₁ with k hk,
  cases h₂ with l hl,
  use k*l,
  rw [hl, hk, mul_assoc],
end

-- 4ª demostración
example
  (h₁ : a ∣ b)
  (h₂ : b ∣ c)
  : a ∣ c :=
begin
  cases h₁ with k hk,
  cases h₂ with l hl,
  use k*l,
  calc c = b * l       : by rw hl
     ... = (a * k) * l : by rw hk
     ... = a * (k * l) : by ring,
end

-- 5ª demostración
example
  (h₁ : a ∣ b)
  (h₂ : b ∣ c)
  : a ∣ c :=
begin
  rcases h₂ with ⟨l, rfl⟩,
  rcases h₁ with ⟨k, rfl⟩,
  use k*l,
  rw mul_assoc,
end

-- 6ª demostración
example
  (h₁ : a ∣ b)
  (h₂ : b ∣ c)
  : a ∣ c :=
exists.elim h₁
  ( assume k,
    assume h₃ : b = a * k,
    show a ∣ c, from
      exists.elim h₂
        ( assume l,
          assume h₄ : c = b * l,
          have h₅ : c = a * (k * l), from
            calc c = b * l       : by rw h₄
               ... = (a * k) * l : by rw h₃
               ... = a * (k * l) : by rw mul_assoc,
          show a ∣ c,
            from exists.intro (k * l) h₅))

-- 7ª demostración
example
  (h₁ : a ∣ b)
  (h₂ : b ∣ c)
  : a ∣ c :=
exists.elim h₁
  (λ k h₃, exists.elim h₂
             (λ l h₄, exists.intro (k * l) (by rw [h₄, h₃, mul_assoc])))

-- 8ª demostración
example
  (h₁ : a ∣ b)
  (h₂ : b ∣ c)
  : a ∣ c :=
-- by library_search
dvd_trans h₁ h₂

-- 9ª demostración
example
  (h₁ : a ∣ b)
  (h₂ : b ∣ c)
  : a ∣ c :=
match h₁, h₂ with
| ⟨k, (h₃ : b = a * k)⟩, ⟨l, (h₄ : c = b * l)⟩ :=
  ⟨k * l, show c = a * (k * l), by simp [h₃, h₄, mul_assoc]⟩
end
