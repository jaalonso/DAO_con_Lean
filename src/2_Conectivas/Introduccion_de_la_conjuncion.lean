-- Introduccion_de_la_conjuncion.lean
-- Introducción de la conjunción.
-- José A. Alonso Jiménez
-- Sevilla, 12 de agosto de 2020
-- ---------------------------------------------------------------------

-- En este relación se muestra distintas formas de demostrar un teorema
-- con introducción de la conjunción.

-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la librería de tácticas.
-- 2. Declarar P y Q como variables sobre proposiciones. 
-- ----------------------------------------------------------------------

import tactic            -- 1
variables (P Q : Prop)   -- 2

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que de P y (P → Q) se deduce P ∧ Q
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

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

-- Comentario
-- ----------

-- La táctica split, cuando la conclusión es una conjunción, aplica la
-- regla de eliminación de la conjunción; es decir, si la conclusión es 
-- (P ∧ Q), entonces crea dos subojetivos: el primero en el que la
-- conclusión es P y el segundo donde es Q.

-- 2ª demostración
-- ===============

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
-- ===============

example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
begin
  have hQ : Q := hPQ hP,
  show P ∧ Q, by exact ⟨hP, hQ⟩,
end

-- 4ª demostración
-- ===============

example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
begin
  show P ∧ Q, by exact ⟨hP, hPQ hP⟩,
end

-- 4ª demostración
-- ===============

example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
begin
  exact ⟨hP, hPQ hP⟩,
end

-- 5ª demostración
-- ===============

example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
by exact ⟨hP, hPQ hP⟩

-- 6ª demostración
-- ===============

example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
⟨hP, hPQ hP⟩

-- 7ª demostración
-- ===============

example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
and.intro hP (hPQ hP)

-- Comentario: Se ha usado el lema
-- + and.intro : P → Q → P ∧ Q 

-- 8ª demostración
-- ===============

example 
  (hP : P) 
  (hPQ : P → Q) 
  : P ∧ Q :=
by tauto


