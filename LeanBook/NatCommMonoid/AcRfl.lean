import LeanBook.NatCommMonoid.Simp

-- 交換法則と結合法則
/-- 足し算の交換法則 -/
theorem MyNat.add_comm (m n : MyNat) : m + n = n + m := by
  induction n
  case zero => simp [MyNat.ctor_eq_zero]
  case succ n ih => simp [ih] -- Try this: simp only [add_succ, ih, succ_add]

theorem MyNat.add_assoc (l m n : MyNat) : (l + m) + n = l + (m + n) := by
  induction n
  case zero => rfl
  case succ n ih => simp [ih] -- Try this: simp only [add_succ, ih]

example (l m n : MyNat) : l + m + n + 3 = m + (l + n) + 3 := calc
  -- 引数を指定することで、どの変数で交換法則を利用するか指定できる
  _ = m + l + n + 3 := by rw [MyNat.add_comm l m]
  -- 引数を指定することで、どの変数で結合法則を利用するか指定できる
  _ = m + (l + n) + 3 := by rw [MyNat.add_assoc m l n]

-- MyNat の足し算が結合法則を満たすことを登録する
instance : Std.Associative (α := MyNat) (· + ·) where
  assoc := MyNat.add_assoc

-- MyNat の足し算が交換法則を満たすことを登録する
instance : Std.Commutative (α := MyNat) (· + ·) where
  comm := MyNat.add_comm

example (l m n : MyNat) : l + m + n + 3 = l + (m + n) + 3 := by
  ac_rfl

-- 練習問題
example (l m n : MyNat) : l + (1 + m) + n = m + (l + n) + 1 := by
  ac_rfl
