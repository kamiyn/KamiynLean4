import LeanBook.NatOrder.NotationSimp
import LeanBook.NatOrder.CompatibleTag

variable {a b m n : MyNat}

/-- 足し算 (l + ·) は順序関係を保つ -/
theorem MyNat.add_le_add_left (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  exists k
  rw [← hk]
  ac_rfl

/-- 足し算 (· + l) は順序関係を保つ -/
theorem MyNat.add_le_add_right (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := calc
  _ = l + m := by ac_rfl
  _ ≤ l + n := by apply MyNat.add_le_add_left h l
  _ = n + l := by ac_rfl

theorem MyNat.add_le_add (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := calc
  _ ≤ m + b := by exact add_le_add_left h2 m
  _ ≤ n + b := by exact add_le_add_right h1 b

example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  apply MyNat.add_le_add_left h

example (hle : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
  apply MyNat.add_le_add_right hle

example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  apply MyNat.add_le_add_left <;> assumption

example (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
  apply MyNat.add_le_add_right <;> assumption

example (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by
  apply MyNat.add_le_add <;> assumption

/-- 関係 a ∼ b が成り立つならば f a ∼ f b が成り立つ というタイプの推論を行う -/
syntax "compatible" : tactic

section
  local macro_rules
    | `(tactic| compatible) =>
      `(tactic| apply MyNat.add_le_add_left <;> assumption)

  -- こちらは証明できる
  example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
    compatible

  example (hle : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
    fail_if_success compatible
    sorry
end

-- macro_rules は同じ構文に対して 複数の構文展開ルールを定義すると、**新しいものから**順に適用され
-- 最初に成功したものを採用する

section
  local macro_rules
    | `(tactic| compatible) =>
      `(tactic| apply MyNat.add_le_add_left <;> assumption)

  local macro_rules
    | `(tactic| compatible) =>
      `(tactic| apply MyNat.add_le_add_right <;> assumption)

  local macro_rules
    | `(tactic| compatible) =>
      `(tactic| apply MyNat.add_le_add <;> assumption)

  example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
    compatible

  example (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
    compatible

  example (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by
    compatible

end

open Lean Elab Tactic in

elab "compatible" : tactic => do
  -- [compatible] 属性が付与された定理をリストアップする
  let taggedDecls ← labelled `compatible
  if taggedDecls.isEmpty then
    throwError "`[compatible]`が付与された定理はありません"
  for decl in taggedDecls do
    let declStx := mkIdent decl
    try
      -- [compatible] 属性が付与された定理 thm に対して apply thm <;> assumption を試す
      evalTactic <| ← `(tactic| apply $declStx <;> assumption)
      -- 成功したら終了する
      return ()
    catch _ =>
      -- 失敗したら単に次の処理に進む
      pure ()
  throwError "ゴールを閉じることができませんでした。"

attribute [compatible] MyNat.add_le_add_left  MyNat.add_le_add_right MyNat.add_le_add

example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by compatible

example (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := by compatible

example (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by compatible

-- ここまで 広義順序。ここから狭義順序 lt になる。(le ではない)
@[compatible]
theorem MyNat.add_lt_add_left {m n : MyNat} (h : m < n) (k : MyNat)
    : k + m < k + n := by
  notation_simp at *
  have : k + m + 1 ≤ k + n := calc
    _ = k + (m + 1) := by ac_rfl
    _ ≤ k + n := by compatible
  assumption

@[compatible]
theorem MyNat.add_lt_add_right {m n : MyNat} (h : m < n) (k : MyNat)
    : m + k < n + k := calc
  _ = k + m := by ac_rfl
  _ < k + n := by compatible
  _ = n + k := by ac_rfl

section

variable (m n k : MyNat) -- 丸カッコ

theorem MyNat.le_of_add_le_add_left : k + m ≤ k + n → m ≤ n := by
  intro h
  rw [MyNat.le_iff_add] at *
  obtain ⟨d, hd⟩ := h
  exists d
  have : m + d + k = n + k := calc
    _ = k + m + d := by ac_rfl
    _ = k + n := by rw [hd]
    _ = n + k := by ac_rfl
  simp_all

theorem MyNat.le_of_add_le_add_right : m + k ≤ n + k → m ≤ n := by
  rw [MyNat.add_comm m k, MyNat.add_comm n k]
  apply MyNat.le_of_add_le_add_left

@[simp] theorem MyNat.add_le_add_iff_left : k + m ≤ k + n ↔ m ≤ n := by
  constructor
  · apply MyNat.le_of_add_le_add_left
  · intro h
    compatible

@[simp] theorem MyNat.add_le_add_iff_right : m + k ≤ n + k ↔ m ≤ n := by
  constructor
  · apply MyNat.le_of_add_le_add_right
  · intro h
    compatible

end -- section

-- 練習問題
variable (m₁ m₂ n₁ n₂ l₁ l₂ : MyNat)

example (h1 : m₁ ≤ m₂) (h2 : n₁ ≤ n₂) (h3 : l₁ ≤ l₂)
  : l₁ + m₁ + n₁ ≤ l₂ + n₂ + m₂ := calc
  _ = l₁ + m₁ + n₁ := by rfl
  -- 右から (nから) 順番に適用していく
  -- 次の行について 本の解答は compatible だった
  _ ≤ l₁ + m₁ + n₂ := by simp_all -- Try this: simp_all only [MyNat.add_le_add_iff_left]
  _ ≤ l₁ + m₂ + n₂ := by simp_all -- try this: simp_all only [MyNat.add_le_add_iff_right,MyNat.add_le_add_iff_left]
  _ ≤ l₂ + m₂ + n₂ := by simp_all -- Try this: simp_all only [MyNat.add_le_add_iff_right]
  _ = l₂ + n₂ + m₂ := by ac_rfl -- 右辺に合わせて 交換法則
