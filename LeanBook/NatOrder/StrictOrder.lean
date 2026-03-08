import LeanBook.NatOrder.OrderDef

/-- m < n を表す -/
def MyNat.lt (m n : MyNat) : Prop := (m + 1) ≤ n

/-- a < b という書き方ができるようにする -/
instance : LT MyNat where
  lt := MyNat.lt

example (m n : MyNat) : m < n ↔ (m + 1) ≤ n := by
  dsimp [(· < ·), MyNat.lt]
  rfl

/-- 1 ≠ 0 が成り立つ -/
@[simp] theorem MyNat.one_neq_zero : 1 ≠ 0 := by
  intro h
  injection h

/-- 0 ≠ 1 が成り立つ -/
@[simp] theorem MyNat.zero_neq_one : 0 ≠ 1 := by
  intro h
  injection h

-- 順序関係において 0 が満たす性質
@[simp] theorem MyNat.zero_le (n : MyNat) : 0 ≤ n := by
  -- ≤ を和の等式に帰着させる
  rw [MyNat.le_iff_add]
  exists n -- k = n とすれば成り立つ
  simp

/-- 0 以下の自然数は 0 しかない -/
theorem MyNat.zero_of_le_zero {n : MyNat} (h : n ≤ 0) : n = 0 := by
  induction n with
  | zero => rfl
  | succ n' _ => -- 矛盾を導きたいので n' と置いた
    -- h : n' + 1 ≤ 0 ← これが重要
    -- ⊢ n' + 1 = 0
    -- Goal が矛盾する状況
    rw [MyNat.le_iff_add] at h -- 仮定 h を和の等式に置き換える
    -- h : ∃ k, n' + 1 + k = 0
    obtain ⟨k, hk⟩ := h
    simp_all -- ここで仮定 hk に + 1 が含まれていて満たせないため矛盾を示せた

@[simp] theorem MyNat.le_zero {n : MyNat} : n ≤ 0 ↔ n = 0 := by
  constructor
  · -- 左から右 ⊢ n ≤ 0 → n = 0
    intro h
    apply MyNat.zero_of_le_zero h
  · -- 右から左 ⊢ n = 0 → n ≤ 0
    intro h
    simp [h]

theorem MyNat.eq_zero_or_pos {n : MyNat} : n = 0 ∨ 0 < n := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- Goal の左側 n + 1 = 0 はありえないので、以降見やすさのため 右側 0 + 1 ≤ n + 1 を選択しておく
    right
    -- まず狭義順序を ≤ で書き換える
    dsimp [(· < ·), MyNat.lt] at * -- Goal と ih とも書き換わる
    -- ih : n = 0 ∨ 0 + 1 ≤ n
    -- ⊢ 0 + 1 ≤ n + 1
    cases ih with
    | inl ih => -- n = 0
      simp_all
    | inr ih => -- ih: 0 + 1 ≤ n
      simp_all [MyNat.le_step] -- ⊢ 0 + 1 ≤ n + 1 を ih と MyNat.le_step で示す

theorem MyNat.eq_or_lt_of_le {m n : MyNat} : n ≤ m → n = m ∨ n < m := by
  intro h
  dsimp [(· < ·), MyNat.lt]
  rw [MyNat.le_iff_add] at *
  -- h : ∃ k, n + k = m
  -- ⊢ n = m ∨ ∃ k, n + 1 + k = m
  obtain ⟨k, hk⟩ := h
  induction k with
  | zero => simp_all
  | succ k _ =>
    have : ∃ k, n + 1 + k = m := by
      exists k
      rw [← hk] -- succ の中のため hk : n + (k + 1) = m
      ac_rfl
    simp_all

/-- 狭義順序は広義順序よりも「強い」 -/
theorem MyNat.le_of_lt {a b : MyNat} (h : a < b) : a ≤ b := by
  -- < を ≤ で置き換え h : a + 1 ≤ b にする
  dsimp [(· < ·), MyNat.lt] at h
  -- a ≤ a + 1 ≤ b と推移的関係を利用することにより a ≤ b を証明する
  calc
    a ≤ a + 1 := by apply MyNat.le_add_one_right
    _ ≤ b     := h

theorem MyNat.le_of_eq_or_lt {m n : MyNat} : n = m ∨ n < m → n ≤ m := by
  intro h
  cases h with
  | inl h => -- n = m
    rw [h] -- m ≤ m に書き換えてしまう
  | inr h => -- n < m
    exact MyNat.le_of_lt h

/-- 広義順序 ≤ は 等号 = と 狭義順序 < で書き換えられる -/
theorem MyNat.le_iff_eq_or_lt {m n : MyNat} : n ≤ m ↔ n = m ∨ n < m :=
  ⟨MyNat.eq_or_lt_of_le, MyNat.le_of_eq_or_lt⟩

theorem MyNat.lt_or_ge (a b : MyNat) : a < b ∨ b ≤ a := by
  dsimp [(· < ·), MyNat.lt]
  induction a with
  | zero =>
    -- このとき 1 ≤ b ∨ b ≤ 0 を示せば十分である
    suffices 1 ≤ b ∨ b ≤ 0 from by simp_all
    -- 任意の自然数はゼロか正であることから b はゼロか1以上である
    have : b = 0 ∨ 0 < b := MyNat.eq_zero_or_pos
    dsimp [(· < ·), MyNat.lt] at this
    -- this : b = 0 ∨ 0 + 1 ≤ b
    -- b = 0 → b ≤ 0 なので、場合分けをすれば示せる
    cases this <;> simp_all
  | succ a ih => -- ih : a + 1 ≤ b ∨ b ≤ a
    -- ⊢ a + 1 + 1 ≤ b ∨ b ≤ a + 1
    cases ih with
    | inr h => -- b ≤ a のとき
      right -- b ≤ a + 1 を示せばよい
      exact le_step h
    | inl h => -- a + 1 ≤ b のとき
      simp[MyNat.le_iff_eq_or_lt] at h -- h : a + 1 = b ∨ a + 1 < b
      cases h with
      | inl h => -- a + 1 = b
        right
        simp_all
      | inr h => -- a + 1 < b
        left
        dsimp [(· < ·), MyNat.lt] at h
        exact h

theorem MyNat.lt_of_not_le {a b : MyNat} (h : ¬ a ≤ b) : b < a := by
  cases (MyNat.lt_or_ge b a) with
  | inl h => assumption
  | inr h => contradiction

theorem MyNat.not_le_of_le {a b : MyNat} (h : a < b) : ¬ b ≤ a := by
  intro hle
  dsimp [(· < ·), MyNat.lt] at h
  rw [MyNat.le_iff_add] at * -- h も goal も和の等式に書き換える
  obtain ⟨k, hk⟩ := h
  obtain ⟨l, hl⟩ := hle
  have : a + (k + l + 1) = a := calc
    _ = a + (k + l + 1) := rfl
    _ = a + 1 + k + l := by ac_rfl
    _ = b + l := by rw [hk]
    _ = a := by rw [hl]
  -- a + (k + l + 1) = a から
  -- (k + l + 1) = 0 すなわち (k + 0) + 1 = 0 という仮定が矛盾
  simp at this

theorem MyNat.lt_iff_le_not_le (a b : MyNat) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  constructor
  · intro h
    simp_all [MyNat.not_le_of_le, MyNat.le_of_lt]
  · intro h
    simp_all [MyNat.lt_of_not_le]

theorem MyNat.le_total (a b : MyNat) : a ≤ b ∨ b ≤ a := by
  cases (MyNat.lt_or_ge a b) <;> simp_all [MyNat.le_of_lt]

-- 練習問題
example (a : MyNat) : a = a + 1 := by
  sorry

example (n : MyNat) : ¬ no + 1 ≤ n := by
  sorry
