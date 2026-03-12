import LeanBook.NatOrder.NotationSimp

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
