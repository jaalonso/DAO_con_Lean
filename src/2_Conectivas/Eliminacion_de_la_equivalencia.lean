-- Eliminacion_de_la_equivalencia.lean
-- Eliminación de la equivalencia.
-- José A. Alonso Jiménez
-- Sevilla, 12 de agosto de 2020
-- ---------------------------------------------------------------------

-- En este relación se muestra distintas formas de demostrar un teorema
-- con eliminación de la equivalencia

-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la librería de tácticas.
-- 2. Declarar P, Q y R como variables sobre proposiciones. 
-- ----------------------------------------------------------------------

import tactic              -- 1
variables (P Q R : Prop)   -- 2

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    P ↔ Q
--    Q → R
-- entonces
--    P → R
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

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

-- Prueba:
/-
  P Q R : Prop,
  h : P ↔ Q,
  hQR : Q → R
  ⊢ P → R
intro hP,
  hP : P
  ⊢ R
apply hQR,
  ⊢ Q
cases h with hPQ hQP,
  hPQ : P → Q,
  hQP : Q → P
  ⊢ Q
apply hPQ,
  ⊢ P
exact hP,
  no goals
-/

-- Comentarios: 
-- + La táctica (cases h with h1 h2), cuando la hipótesis h es una
--   equivalencia aplica la regla de eliminación de la equivalencia; es
--   decir, si h es (P ↔ Q), entonces elimina h y añade las hipótesis
--   (h1 : P → Q) y (h2 : Q → P).

-- 2ª demostración (simplificando los últimos pasos de la anterior)
-- ================================================================

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

-- Prueba:
/-
  P Q R : Prop,
  h : P ↔ Q,
  hQR : Q → R
  ⊢ P → R
intro hP,
  hP : P
  ⊢ R
apply hQR,
  ⊢ Q
cases h with hPQ hQP,
  hPQ : P → Q,
  hQP : Q → P
  ⊢ Q
exact hPQ hP,
  no goals
-/

-- 3ª demostración (simplificando los últimos pasos de la anterior)
-- ================================================================

example 
  (h : P ↔ Q) 
  (hQR : Q → R) 
  : P → R :=
begin
  intro hP,
  exact hQR (h.1 hP),
end

-- Comentarios:
-- + Si h es la equivalencia (P ↔ Q), entonces h.1 es (P → Q) y h.2 es 
--   (Q → P). 

-- 4ª demostración (por un término)
-- ================================

example 
  (h : P ↔ Q) 
  (hQR : Q → R) 
  : P → R :=
λ hP, hQR (h.1 hP)

-- 5ª demostración (por reescritura)
-- =================================

example 
  (h : P ↔ Q) 
  (hQR : Q → R) 
  : P → R :=
begin
  rw h,
  exact hQR,
end

-- Prueba:
/-
  P Q R : Prop,
  h : P ↔ Q,
  hQR : Q → R
  ⊢ P → R
rw h,
  ⊢ Q → R
exact hQR,
  no goals
-/

-- Comentarios:
-- + La táctica (rw h), cuando h es una equivalencia como (P ↔ Q),
--   sustituye en la conclusión P por Q.

-- 6ª demostración (por reescritura en hipótesis)
-- ==============================================

example 
  (h : P ↔ Q) 
  (hQR : Q → R) 
  : P → R :=
begin
  rw ← h at hQR,
  exact hQR,
end

-- Prueba:
/-
  P Q R : Prop,
  h : P ↔ Q,
  hQR : Q → R
  ⊢ P → R
rw ← h at hQR,
  hQR : P → R
  ⊢ P → R  
exact hQR,
  no goals
-/

-- Comentarios:
-- + La táctica (rw ← h at h'), cuando h es una equivalencia como (P ↔- Q),
--   sustituye en la  hipótesis h' la fórmula Q por P.

-- 7ª demostración (estructurada)
-- ==============================

example 
  (h : P ↔ Q) 
  (hQR : Q → R) 
  : P → R :=
begin
  assume hP : P,
  have hQ : Q, from h.1 hP,
  show R, from hQR hQ,
end

-- 8ª demostración (automática)
-- ============================

example 
  (h : P ↔ Q) 
  (hQR : Q → R) 
  : P → R :=
by tauto


