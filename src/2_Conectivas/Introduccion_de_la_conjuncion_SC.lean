-- Introducción de la conjunción en Lean
-- =====================================

-- Demostrar que de P y (P → Q) se deduce P ∧ Q.

import tactic            

variables (P Q : Prop)   

-- 1ª demostración
example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
begin
  split,
  { exact hP },
  { apply hPQ,
    exact hP },
end

-- 2ª demostración
example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
begin
  split,
  { exact hP },
  { exact hPQ hP },
end

-- 3ª demostración
example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
begin
  have hQ : Q := hPQ hP,
  show P ∧ Q, by exact ⟨hP, hQ⟩,
end

-- 4ª demostración
example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
begin
  show P ∧ Q, by exact ⟨hP, hPQ hP⟩,
end

-- 5ª demostración
example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
begin
  exact ⟨hP, hPQ hP⟩,
end

-- 6ª demostración
example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
by exact ⟨hP, hPQ hP⟩

-- 7ª demostración
example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
⟨hP, hPQ hP⟩

-- 8ª demostración
example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
and.intro hP (hPQ hP)

-- 9ª demostración
example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
by tauto

-- 10ª demostración
example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
by finish


