-- Eliminación de la equivalencia en Lean
-- ======================================

-- Demostrar que si
--    P ↔ Q
--    Q → R
-- entonces
--    P → R

import tactic              
variables (P Q R : Prop)   

-- 1ª demostración
example 
  (h : P ↔ Q) 
  (hQR : Q → R) 
  : P → R :=
begin
  intro hP,
  apply hQR,
  cases h with hPQ hQP,
  apply hPQ,
  exact hP,
end

-- 2ª demostración
example 
  (h : P ↔ Q) 
  (hQR : Q → R) 
  : P → R :=
begin
  intro hP,
  apply hQR,
  cases h with hPQ hQP,
  exact hPQ hP,
end

-- 3ª demostración
example 
  (h : P ↔ Q) 
  (hQR : Q → R) 
  : P → R :=
begin
  intro hP,
  exact hQR (h.1 hP),
end

-- 4ª demostración
example 
  (h : P ↔ Q) 
  (hQR : Q → R) 
  : P → R :=
λ hP, hQR (h.1 hP)

-- 5ª demostración
example 
  (h : P ↔ Q) 
  (hQR : Q → R) 
  : P → R :=
begin
  rw h,
  exact hQR,
end

-- 6ª demostración
example 
  (h : P ↔ Q) 
  (hQR : Q → R) 
  : P → R :=
begin
  rw ← h at hQR,
  exact hQR,
end

-- 7ª demostración
example 
  (h : P ↔ Q) 
  (hQR : Q → R) 
  : P → R :=
begin
  assume hP : P,
  have hQ : Q, from h.1 hP,
  show R, from hQR hQ,
end

-- 8ª demostración
example 
  (h : P ↔ Q) 
  (hQR : Q → R) 
  : P → R :=
assume hP, hQR (h.1 hP)

-- 9ª demostración
example 
  (h : P ↔ Q) 
  (hQR : Q → R) 
  : P → R :=
by tauto

-- 10ª demostración
example 
  (h : P ↔ Q) 
  (hQR : Q → R) 
  : P → R :=
by finish


