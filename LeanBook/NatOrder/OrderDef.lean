import LeanBook.NatOrder.AddCancel

/-- 自然数上の広義の順序関係 -/
inductive MyNat.le (n : MyNat) : MyNat → Prop
  /-- ∀ n, n ≤ n-/
  | refl : MyNat.le n n
  /-- n ≤ m ならば n ≤ m + 1 -/
  | step {m : MyNat} : MyNat.le n m → MyNat.le n (m + 1)

/-- MyNat.le を ≤ で表せるようにする -/
instance : LE MyNat where
  le := MyNat.le

-- 帰納法での証明をテンプレート
-- example (m n : MyNat) (P : MyNat → MyNat → Prop) (h : m ≤ n) : P m n := by
--   induction h with
--   | refl =>
--     -- m = n の場合
--     guard_target =ₛ P m m
--     sorry
--   -- @ は暗黙引数を明示的引数に変えるための構文
--   | @step n h ih =>
--     -- P m n → P m (n + 1) を示す
--     guard_hyp ih : P m n
--     guard_target =ₛ P m (n + 1)
--     sorry

@[induction_eliminator]
def MyNat.le.recAux {n b : MyNat}
    {motive : (a : MyNat) → n ≤ a → Prop}
    (refl : motive n MyNat.le.refl)
    (step : ∀ {m : MyNat} (a : n ≤ m), motive m a → motive (m + 1) (MyNat.le.step a))
    (t : n ≤ b) :
  motive b t := by
  induction t with
  | refl => exact refl
  | @step c h ih =>
    exact step (a := h) ih

/-- 反射律 -/
theorem MyNat.le_refl (n : MyNat) : n ≤ n := by
  exact MyNat.le.refl

variable {m n k : MyNat}

theorem MyNat.le_step (h : n ≤ m) : n ≤ m + 1 := by
  apply MyNat.le.step
  exact h

/-- 推移律 -/
theorem MyNat.le_trans (hnm : n ≤ m) (hmk : m ≤ k) : n ≤ k := by
  -- 順序関係を帰納的に定義したので、順序に対する帰納法ができる
  induction hmk with
  | refl => exact hnm
  | @step k hmk ih =>
    exact MyNat.le_step ih

attribute [refl] MyNat.le_refl

theorem MyNat.le_add_one_right (n : MyNat) : n ≤ n + 1 := by
  apply MyNat.le_step
  rfl -- 反射律を 登録したので rfl で示せるようになった

/-- MyNat.le を「推移的な二項関係」として登録する -/
instance : Trans (· ≤ · : MyNat → MyNat → Prop) (· ≤ ·) (· ≤ ·) where
  trans := MyNat.le_trans

-- calc が使えるようになった
theorem MyNat.le_add_one_left (n : MyNat) : n ≤ 1 + n := calc
  _ ≤ n + 1 := by apply le_add_one_right
  _ = 1 + n := by ac_rfl

-- simp から再利用可能にする
-- 命題 P を登録すると P ↔ True という形の書き換えルールが生成される
-- ¬ P を登録すると P ↔ False という形の書き換えルールが生成される
attribute [simp] MyNat.le_refl MyNat.le_add_one_right MyNat.le_add_one_left

/-- a ≤ b から和の等式を導く -/
theorem MyNat.le.dest (h : n ≤ m) : ∃ k, n + k = m := by
  induction h with
  | refl => exists 0
  | @step l h ih =>
    obtain ⟨k, ih⟩ := ih
    exists k + 1
    -- この時点で
    -- ih : n + k = l
    -- ⊢ n + (k + 1) = l + 1
    rw [← ih]
    -- ⊢ n + (k + 1) = n + k + 1
    ac_rfl

theorem MyNat.le_add_right (n m : MyNat) : n ≤ n + m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [show n + (k + 1) = (n + k) + 1 from by ac_rfl]
    exact MyNat.le_step ih

/-- 和の等式から a ≤ b を導く -/
theorem MyNat.le.intro (h : n + k = m) : n ≤ m := by
  rw [← h]
  apply MyNat.le_add_right

theorem MyNat.le_iff_add : n ≤ m ↔ ∃ k, n + k = m := by
  constructor
  · -- 左から右 ⊢ n ≤ m → ∃ k, n + k = m
    intro h
    exact MyNat.le.dest h
  · -- 右から左 ⊢ (∃ k, n + k = m) → n ≤ m
    intro h
    obtain ⟨k, hk⟩ := h
    exact MyNat.le.intro hk

-- 練習問題
example : 1 ≤ 4 := by
  rw [MyNat.le_iff_add] -- ⊢ ∃ k, 1 + k = 4 に変換
  exists 3

example : 1 ≤ 4 := by
  apply MyNat.le_step
  apply MyNat.le_step
  apply MyNat.le_step
  rfl

-- repeat + first 構文が存在する。LISP の末尾再帰のように 実行したい というプロンプトから
example : 1 ≤ 4 := by
  -- 1 ≤ 1 に到達するまで le_step を繰り返し適用する
  repeat (first | rfl | apply MyNat.le_step)
