import LeanBook.NatOrder.StrictOrder

theorem MyNat.lt_def (m n : MyNat) : m < n ↔ m + 1 ≤ n := by
  rfl

section
  /- ## simp で展開するテスト -/
  -- この section の中でのみ simp に登録する
  attribute [local simp] MyNat.lt_def

  example (m n : MyNat) : m < n := by
    simp -- simp は 登録されているすべての simp ルールを展開する。どれを展開するかがこの行で直観的にわからない
    guard_target =ₛ m + 1 ≤ n
    sorry
  end
