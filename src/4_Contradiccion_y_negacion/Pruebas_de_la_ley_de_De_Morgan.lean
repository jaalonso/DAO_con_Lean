-- Pruebas de la ley de De Morgan: ¬(P ∧ Q) ↔ ¬P ∨ ¬Q
-- ==================================================

import tactic
variables (P Q : Prop)

-- ----------------------------------------------------
-- Ejercicio. Demostrar que
--    ¬(P ∧ Q) ↔ ¬P ∨ ¬Q
-- ----------------------------------------------------

-- 1ª demostración
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
begin
  split,
  { intro h,
    by_cases hP : P,
    { right,
      intro hQ,
      apply h,
      split,
      { exact hP, },
      { exact hQ, }},
    { left,
      exact hP, }},
  { intros h h',
    cases h' with hP hQ,
    cases h with hnP hnQ,
    { exact hnP hP, },
    { exact hnQ hQ, }},
end

-- 2ª demostración
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
begin
  split,
  { intro h,
    by_cases hP : P,
    { right,
      intro hQ,
      exact h ⟨hP, hQ⟩, },
    { left,
      exact hP, }},
  { rintros (hnP | hnQ) ⟨hP, hQ⟩,
    { exact hnP hP, },
    { exact hnQ hQ, }},
end

-- 3ª demostración
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
iff.intro
  ( assume h : ¬(P ∧ Q),
    show ¬P ∨ ¬Q, from
      or.elim (classical.em P)
        ( assume hP : P,
          have hnQ : ¬Q,
            { assume hQ : Q,
              have hPQ: P ∧ Q,
                from and.intro hP hQ,
              show false,
                from h hPQ },
          show ¬P ∨ ¬Q,
            from or.inr hnQ)
        ( assume hnP : ¬P,
          show ¬P ∨ ¬Q,
            from or.inl hnP))
  ( assume h: ¬P ∨ ¬Q,
    show ¬(P ∧ Q), from
      assume hPQ : P ∧ Q,
      show false, from
        or.elim h
          ( assume hnP: ¬P,
            show false,
              from hnP (and.left hPQ))
          ( assume hnQ: ¬Q,
            show false,
              from hnQ (and.right hPQ)))

-- 4ª demostración
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
iff.intro
  ( assume h : ¬(P ∧ Q),
    show ¬P ∨ ¬Q, from
      or.elim (classical.em P)
        ( assume hP : P,
          have hnQ : ¬Q,
            { assume hQ : Q,
              have hPQ: P ∧ Q,
                from and.intro hP hQ,
              show false,
                from h hPQ },
          show ¬P ∨ ¬Q,
            from or.inr hnQ)
        or.inl)
  ( assume h: ¬P ∨ ¬Q,
    show ¬(P ∧ Q), from
      assume hPQ : P ∧ Q,
      show false, from
        or.elim h
          ( assume hnP: ¬P,
            show false,
              from hnP (and.left hPQ))
          (λ hnQ, hnQ (and.right hPQ)))

-- 5ª demostración
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
iff.intro
  ( assume h : ¬(P ∧ Q),
    show ¬P ∨ ¬Q, from
      or.elim (classical.em P)
        ( assume hP : P,
          have hnQ : ¬Q,
            { assume hQ : Q,
              have hPQ: P ∧ Q,
                from and.intro hP hQ,
              show false,
                from h hPQ },
          or.inr hnQ)
        or.inl)
  ( assume h: ¬P ∨ ¬Q,
    show ¬(P ∧ Q), from
      assume hPQ : P ∧ Q,
      show false, from
        or.elim h
          (λ hnP, hnP (and.left hPQ))
          (λ hnQ, hnQ (and.right hPQ)))

-- 6ª demostración
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
iff.intro
  ( assume h : ¬(P ∧ Q),
    show ¬P ∨ ¬Q, from
      or.elim (classical.em P)
        ( assume hP : P,
          have hnQ : ¬Q,
            { assume hQ : Q,
              show false,
                from h (and.intro hP hQ) },
          or.inr hnQ)
        or.inl)
  ( assume h: ¬P ∨ ¬Q,
    show ¬(P ∧ Q), from
      λ hPQ, or.elim h (λ hnP, hnP (and.left hPQ))
                       (λ hnQ, hnQ (and.right hPQ)))

-- 7ª demostración
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
iff.intro
  ( assume h : ¬(P ∧ Q),
    show ¬P ∨ ¬Q, from
      or.elim (classical.em P)
        ( assume hP : P,
          or.inr (λ hQ, h (and.intro hP hQ)))
        or.inl)
  ( λ h hPQ, or.elim h (λ hnP, hnP (and.left hPQ))
                       (λ hnQ, hnQ (and.right hPQ)))

-- 8ª demostración
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
iff.intro
  ( assume h : ¬(P ∧ Q),
    show ¬P ∨ ¬Q, from
      or.elim (classical.em P)
        (λ hP, or.inr (λ hQ, h (and.intro hP hQ)))
        or.inl)
  ( λ h hPQ, or.elim h (λ hnP, hnP (and.left hPQ))
                       (λ hnQ, hnQ (and.right hPQ)))

-- 9ª demostración
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
iff.intro
  (λ h, or.elim (classical.em P)
          (λ hP, or.inr (λ hQ, h (and.intro hP hQ)))
          or.inl)
  (λ h hPQ, or.elim h
              (λ hnP, hnP (and.left hPQ))
              (λ hnQ, hnQ (and.right hPQ)))

-- 10ª demostración
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
⟨λ h, or.elim (classical.em P) (λ hP, or.inr (λ hQ, h ⟨hP, hQ⟩)) or.inl,
 λ h hPQ, or.elim h (λ hnP, hnP hPQ.1) (λ hnQ, hnQ hPQ.2)⟩

-- 11ª demostración
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
-- by library_search
not_and_distrib

-- 12ª demostración
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
-- by hint
by finish
