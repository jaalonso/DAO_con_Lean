-- Eliminación de la disyunción en Lean
-- ====================================

-- Demostrar que si
--    P → R y 
--    Q → R 
-- entonces
--    P ∨ Q → R 

import tactic              

variables (P Q R : Prop)   

-- 1ª demostración
example 
  (hPR : P → R) 
  (hQR : Q → R) 
  : P ∨ Q → R :=
begin
  intro h,
  cases h with hP hQ,
  { exact hPR hP },
  { exact hQR hQ },
end

-- 2ª demostración
example 
  (hPR : P → R) 
  (hQR : Q → R) 
  : P ∨ Q → R :=
begin
  rintro (hP | hQ),
  { exact hPR hP },
  { exact hQR hQ },
end

-- 3ª demostración
example 
  (hPR : P → R) 
  (hQR : Q → R) 
  : P ∨ Q → R :=
λ h, or.elim h hPR hQR 

-- 4ª demostración
example 
  (hPR : P → R) 
  (hQR : Q → R) 
  : P ∨ Q → R :=
or.rec hPR hQR

-- 5ª demostración
example 
  (hPR : P → R) 
  (hQR : Q → R) 
  : P ∨ Q → R :=
by tauto

-- 6ª demostración
example 
  (hPR : P → R) 
  (hQR : Q → R) 
  : P ∨ Q → R :=
by finish
