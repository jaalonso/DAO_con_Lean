-- CNS de divisible por cero
-- =========================

import tactic
import algebra.divisibility

variable (a : ℤ)

-- ----------------------------------------------------
-- Ejercicio. Demostrar que
--     0 ∣ a ↔ a = 0
-- ----------------------------------------------------

-- 1ª demostración
example : 0 ∣ a ↔ a = 0 :=
begin
  -- unfold has_dvd.dvd,
  split,
  { intro h,
    cases h with k hk,
    rw hk,
    rw zero_mul, },
  { intro h,
    use 0,
    rw h,
    rw zero_mul, },
end

-- 2ª demostración
example : 0 ∣ a ↔ a = 0 :=
begin
  split,
  { intro h,
    rcases h with ⟨k, rfl⟩,
    rw zero_mul, },
  { intro h,
    rw h, },
end

-- 3ª demostración
example : 0 ∣ a ↔ a = 0 :=
begin
  split,
  { rintro ⟨k, rfl⟩,
    ring, },
  { rintro rfl,
    use 0,
    ring, },
end

-- 4ª demostración
example : 0 ∣ a ↔ a = 0 :=
iff.intro
  ( assume h: 0 ∣ a,
    show a = 0, from
      dvd.elim h
        ( assume k,
          assume hk : a = 0 * k,
          show a = 0, from
            calc a = 0 * k : hk
               ... = 0     : zero_mul k))
  ( assume h : a = 0,
    have h1 : 0 * 0 = a, from
      calc 0 * 0 = 0 : zero_mul 0
             ... = a : by rw ← h,
    show 0 ∣ a, from dvd.intro 0 h1)

-- 5ª demostración
example : 0 ∣ a ↔ a = 0 :=
iff.intro
  ( assume h: 0 ∣ a,
    show a = 0, from
      dvd.elim h
        ( assume k,
          assume hk : a = 0 * k,
          show a = 0, from
            calc a = 0 * k : hk
               ... = 0     : zero_mul k))
  ( assume h : a = 0,
    show 0 ∣ a,
      from by rw h)

-- 6ª demostración
example : 0 ∣ a ↔ a = 0 :=
iff.intro
  ( assume h: 0 ∣ a,
    show a = 0, from
      dvd.elim h
        ( assume k,
          assume hk : a = 0 * k,
          show a = 0,
            from by rw [hk, zero_mul]))
  ( assume h : a = 0,
    show 0 ∣ a,
      from by rw h)

-- 7ª demostración
example : 0 ∣ a ↔ a = 0 :=
iff.intro
  (λ h, dvd.elim h (λ k hk, by rw [hk, zero_mul]))
  (λ h, by rw h)

-- 8ª demostración
example : 0 ∣ a ↔ a = 0 :=
⟨λ h, dvd.elim h (λ k hk, by rw [hk, zero_mul]),
 λ h, by rw h⟩

-- 9ª demostración
example : 0 ∣ a ↔ a = 0 :=
-- by library_search
zero_dvd_iff

-- 8ª demostración
example : 0 ∣ a ↔ a = 0 :=
-- by hint
by norm_num

-- 10ª demostración
example : 0 ∣ a ↔ a = 0 :=
by finish

-- 11ª demostración
example : 0 ∣ a ↔ a = 0 :=
by simp
