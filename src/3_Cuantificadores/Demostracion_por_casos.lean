-- Demostración por casos: P → R, ¬P → Q, Q → R ⊢ R
-- ================================================

import tactic

variables (P Q R : Prop)

open_locale classical

-- ----------------------------------------------------
-- Ejercicio. Demostrar que
--    P → R, ¬P → Q, Q → R ⊢ R
-- ----------------------------------------------------

-- 1ª demostración
example
  (hPR : P → R)
  (hPQ : ¬ P → Q)
  (hQR : Q → R)
  : R :=
begin
  by_cases hP : P,
  { apply hPR,
    exact hP, },
  { apply hQR,
    apply hPQ,
    exact hP, },
end

-- 2ª demostración
example
  (hPR : P → R)
  (hPQ : ¬ P → Q)
  (hQR : Q → R)
  : R :=
begin
  by_cases hP : P,
  { exact hPR hP, },
  { exact hQR (hPQ hP), },
end

-- 3ª demostración
example
  (hPR : P → R)
  (hPQ : ¬ P → Q)
  (hQR : Q → R)
  : R :=
dite P (λ h, hPR h) (λ h, hQR (hPQ h))

-- 4ª demostración
example
  (hPR : P → R)
  (hPQ : ¬ P → Q)
  (hQR : Q → R)
  : R :=
have h : P ∨ ¬P,
  from em P,
or.elim h
  ( assume hP : P,
    show R,
      from hPR hP)
  ( assume hnP : ¬P,
    have hQ : Q,
      from hPQ hnP,
    show R,
      from hQR hQ)

-- 5ª demostración
example
  (hPR : P → R)
  (hPQ : ¬ P → Q)
  (hQR : Q → R)
  : R :=
have h : P ∨ ¬P,
  from em P,
or.elim h
  ( assume hP : P,
    show R,
      from hPR hP)
  ( assume hnP : ¬P,
    have hQ : Q,
      from hPQ hnP,
    hQR hQ)

-- 6ª demostración
example
  (hPR : P → R)
  (hPQ : ¬ P → Q)
  (hQR : Q → R)
  : R :=
have h : P ∨ ¬P,
  from em P,
or.elim h
  ( assume hP : P,
    show R,
      from hPR hP)
  ( assume hnP : ¬P,
    hQR (hPQ hnP))

-- 7ª demostración
example
  (hPR : P → R)
  (hPQ : ¬ P → Q)
  (hQR : Q → R)
  : R :=
have h : P ∨ ¬P,
  from em P,
or.elim h
  ( assume hP : P,
    show R,
      from hPR hP)
  (λ hnP, hQR (hPQ hnP))

-- 8ª demostración
example
  (hPR : P → R)
  (hPQ : ¬ P → Q)
  (hQR : Q → R)
  : R :=
have h : P ∨ ¬P,
  from em P,
or.elim h
  ( assume hP : P,
    hPR hP)
  (λ hnP, hQR (hPQ hnP))

-- 9ª demostración
example
  (hPR : P → R)
  (hPQ : ¬ P → Q)
  (hQR : Q → R)
  : R :=
have h : P ∨ ¬P,
  from em P,
or.elim h
  (λ hP, hPR hP)
  (λ hnP, hQR (hPQ hnP))

-- 10ª demostración
example
  (hPR : P → R)
  (hPQ : ¬ P → Q)
  (hQR : Q → R)
  : R :=
or.elim (em P) (λ h, hPR h) (λ h, hQR (hPQ h))

-- 11 demostración
example
  (hPR : P → R)
  (hPQ : ¬ P → Q)
  (hQR : Q → R)
  : R :=
-- by hint
by tauto

-- 12ª demostración
example
  (hPR : P → R)
  (hPQ : ¬ P → Q)
  (hQR : Q → R)
  : R :=
by finish
