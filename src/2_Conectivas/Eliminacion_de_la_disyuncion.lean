-- Eliminacion_de_la_disyuncion.lean
-- Eliminación de la disyunción.
-- José A. Alonso Jiménez
-- Sevilla, 13 de agosto de 2020
-- ---------------------------------------------------------------------

-- En este relación se muestra distintas formas de demostrar un teorema
-- con eliminación de la disyunción

-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la librería de tácticas.
-- 2. Declarar P, Q y R como variables sobre proposiciones. 
-- ----------------------------------------------------------------------

import tactic              -- 1
variables (P Q R : Prop)   -- 2

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    P → R y 
--    Q → R 
-- entonces
--    P ∨ Q → R 
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

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

-- Comentario
-- ----------

-- La táctica (cases h with h1 h2), cuando la hipótesis h es una
-- disyunción aplica la regla de eliminación de la disyunción; es decir,
-- si h es (P ∨ Q), entonces elimina h y crea dos casos: uno añadiendo
-- la hipótesis (h1 : P)   y otro añadiendo la hipótesis (h2 : Q).   

-- 2ª demostración
-- ===============

example 
  (hPR : P → R) 
  (hQR : Q → R) 
  : P ∨ Q → R :=
begin
  rintro (hP | hQ),
  { exact hPR hP },
  { exact hQR hQ },
end

-- Comentario
-- ----------

-- La táctica (rintro (h1 | h2)), cuando la conclusión es una
-- implicación cuyo antecedente es una disyunción, aplica las regla des
-- introducción de la implicación y de eliminación de la disyunción; es
-- decir, si la conclusión es (P ∨ Q → R) entonces crea dos casos: en el
-- primero añade la hipótesis (h1 : P) y cambia a conclusión a R; en el
-- segundo añade la hipótesis (h2 : Q) y cambia la conclusión a R.

-- 3ª demostración
-- ===============

example 
  (hPR : P → R) 
  (hQR : Q → R) 
  : P ∨ Q → R :=
λ h, or.elim h hPR hQR 

-- Comentario: Se ha usado el lema
-- + or.elim : P ∨ Q → (P → R) → (Q → R) → R

-- 3ª demostración
-- ===============

example 
  (hPR : P → R) 
  (hQR : Q → R) 
  : P ∨ Q → R :=
or.rec hPR hQR

-- Comentario: Se ha usado el lema
-- + or.rec    : (P → R) → (Q → R) → P ∨ Q → R 

-- 4ª demostración
-- ===============

example 
  (hPR : P → R) 
  (hQR : Q → R) 
  : P ∨ Q → R :=
by tauto
