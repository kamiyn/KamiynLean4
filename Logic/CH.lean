-- カリー・ハワード同型対応
-- 命題は型で、証明はその項 :
-- P : Prop を証明することは、 Pという型を持つ項を構成すること
-- P が偽であるならば P という型に 項 は存在しない

/-- 1 + 1 = 2 という命題の証明 -/
theorem one_add_one_eq_two : 1 + 1 = 2 := by
  -- 1, 2 は Lean で標準的に用意されている自然数
  -- 1 + 1 は定義上 2
  rfl

#check one_add_one_eq_two

#check (by rfl : 1 + 1 = 2)

-- rfl を使わない展開
theorem one_add_one_eq_two_expanded : 1 + 1 = 2 := by
  -- 1 + 1 を Nat.add 1 (Nat.succ 0) と解釈
  -- 定義により Nat.succ (Nat.add 1 0) に簡約される
  show Nat.succ (1 + 0) = 2
  -- Nat.add 1 0 は 1 なので、Nat.succ 1 になる
  show Nat.succ 1 = 2
  -- Nat.succ 1 は定義上 2 である
  show 2 = 2
  exact Eq.refl 2

/-- P → Q の正体 -/
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  -- h は関数である
  -- h が P の証明 hp を受け取って Q の証明を返す
  exact h hp

/-- Nat 上の恒等関数 -/
def idOnNat : Nat → Nat := by?
  intro n
  exact n

#eval idOnNat 42

example (P Q : Prop) (hp : P) : Q → P :=
  sorry
