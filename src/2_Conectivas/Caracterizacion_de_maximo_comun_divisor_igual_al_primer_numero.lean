-- Caracterizacion_de_maximo_comun_divisor_igual_al_primer_numero.lean
-- Caracterización de máximo común divisor igual al primer número.
-- José A. Alonso Jiménez
-- Sevilla, 25 de agosto de 2020
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a y b son números naturales, entonces
--    a ∣ b ↔ gcd a b = a
-- ----------------------------------------------------------------------

import data.nat.gcd

open nat

variables (a b : ℕ)

-- 1ª demostración
-- ===============

example : a ∣ b ↔ gcd a b = a :=
begin
  have h1 : gcd a b ∣ a ∧ gcd a b ∣ b,
  { rw ← dvd_gcd_iff, },
  split,
  { intro h2,
    apply dvd_antisymm h1.left,
    rw dvd_gcd_iff,
    exact ⟨dvd_refl a, h2⟩, },
  { intro h3,
    rw ← h3,
    exact h1.right, },
end

-- Comentarios: 
-- + La orden (open nat) abre el es espacio de nombre de los naturales. 
-- + La relación (a ∣ b) se verifica si a divide a b.
-- + (gcd a b) es el máximo común divisor de a y b.  
-- + Si h es la conjunción (P ∧ Q), entonces h.letf es P y h.right es
--   Q. 
-- + Se han usado los lemas
--   + dvd_gcd_iff : c ∣ gcd a b ↔ c ∣ a ∧ c ∣ b
--   + dvd_antisymm : a ∣ b → b ∣ a → a = b 
--   + dvd_refl a : a ∣ a

-- 2ª demostración
-- ===============

example : a ∣ b ↔ gcd a b = a :=
gcd_eq_left_iff_dvd

-- Comentario: Se ha usado el lema
-- + gcd_eq_left_iff_dvd : a ∣ b ↔ gcd a b = a 




