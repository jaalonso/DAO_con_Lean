-- La suma de no negativos es expansiva 
-- ====================================

-- Demostrar si a y b son números naturales y a es no
-- negativo, entonces b ≤ a + b

import data.real.basic

variables {a b : ℝ}

-- 1ª demostración
example  
  (ha : 0 ≤ a) 
  : b ≤ a + b :=
begin
  calc b = 0 + b : by rw zero_add
     ... ≤ a + b : by exact add_le_add_right ha b,
end

-- 2ª demostración
example  
  (ha : 0 ≤ a) 
  : b ≤ a + b :=
begin
  calc b = 0 + b : (zero_add b).symm
     ... ≤ a + b : add_le_add_right ha b,
end

-- 3ª demostración
example  
  (ha : 0 ≤ a) 
  : b ≤ a + b :=
begin
  calc b = 0 + b : by ring
     ... ≤ a + b : add_le_add_right ha b,
end

-- 4ª demostración
example  
  (ha : 0 ≤ a) 
  : b ≤ a + b :=
by simp [ha]

-- 5ª demostración
example  
  (ha : 0 ≤ a) 
  : b ≤ a + b :=
le_add_of_nonneg_left ha

-- 6ª demostración
example  
  (ha : 0 ≤ a) 
  : b ≤ a + b :=
by linarith

-- 7ª demostración
example  
  (ha : 0 ≤ a) 
  : b ≤ a + b :=
by finish

-- Demostrar si a y b son números naturales y b es no
-- negativo, entonces a ≤ a + b

-- 1ª demostración
example  
  (hb : 0 ≤ b) 
  : a ≤ a + b :=
begin
  calc a = a + 0 : by rw add_zero
     ... ≤ a + b : by exact add_le_add_left hb a,
end

-- 2ª demostración
example  
  (hb : 0 ≤ b) 
  : a ≤ a + b :=
begin
  calc a = a + 0 : (add_zero a).symm
     ... ≤ a + b : add_le_add_left hb a,
end

-- 3ª demostración
example  
  (hb : 0 ≤ b) 
  : a ≤ a + b :=
begin
  calc a = a + 0 : by ring
     ... ≤ a + b : add_le_add_left hb a,
end

-- 4ª demostración
example  
  (hb : 0 ≤ b) 
  : a ≤ a + b :=
by simp [hb]

-- 5ª demostración
example  
  (hb : 0 ≤ b) 
  : a ≤ a + b :=
le_add_of_nonneg_right hb

-- 6ª demostración
example  
  (hb : 0 ≤ b) 
  : a ≤ a + b :=
by linarith

-- 7ª demostración
example  
  (hb : 0 ≤ b) 
  : a ≤ a + b :=
by finish

-- 8ª demostración
example  
  (hb : 0 ≤ b) 
  : a ≤ a + b :=
begin
  rw add_comm,
  apply le_add_of_nonneg_left,
  exact hb,
end

-- 9ª demostración
example  
  (hb : 0 ≤ b) 
  : a ≤ a + b :=
begin
  rw add_comm,
  exact le_add_of_nonneg_left hb,
end
