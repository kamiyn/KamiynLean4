import LeanBook.NatOrder.OrdMonoid

variable {n m k : MyNat}

-- 狭義順序と広義順序の推移律
theorem MyNat.lt_trans (h₁ : n < m) (h₂ : m < k) : n < k := by
  notation_simp at *
  have : n + 1 ≤ k := calc
    _ ≤ m := by exact h₁;
    _ ≤ m + 1 := by simp_all
    _ ≤ k := by exact h₂
  assumption

theorem MyNat.lt_of_le_of_lt (h₁ : n ≤ m) (h₂ : m < k) : n < k := by
  notation_simp at *
  have : n + 1 ≤ k := calc
    _ ≤ m + 1 := by compatible
    _ ≤ k := h₂
  assumption

theorem MyNat.lt_of_lt_of_le (h₁ : n < m) (h₂ : m ≤ k) : n < k := by
  notation_simp at *
  have : n + 1 ≤ k := calc
    _ ≤ m := h₁
    _ ≤ k := h₂
  assumption

instance : Trans (· < · : MyNat → MyNat → Prop) (· < ·) (· < ·) where
  trans := MyNat.lt_trans

instance : Trans (· ≤ · : MyNat → MyNat → Prop) (· < ·) (· < ·) where
  trans := MyNat.lt_of_le_of_lt

instance : Trans (· < · : MyNat → MyNat → Prop) (· ≤ ·) (· < ·) where
  trans := MyNat.lt_of_lt_of_le

-- 狭義順序の非反射律
-- @[simp] theorem MyNat.lt_irrefl (n : MyNat) : ¬ n < n := by
--   intro h
--   notation_simp at h
--   rw [MyNat.le_iff_add] at h
--   obtain ⟨k, hk⟩ := h
--   have : n + (k + 1) = n := calc
--     _ = n + 1 + k := by ac_rfl
--     _ = n := by rw [hk]
--   simp_all

-- 上記 calc の方が素直なのかもしれない
@[simp] theorem MyNat.lt_irrefl (n : MyNat) : ¬ n < n := by
  intro h
  notation_simp at h
  rw [MyNat.le_iff_add] at h
  obtain ⟨k, hk⟩ := h -- hk : n + 1 + k = n
  have : 1 + k = 0 := by
    rw [show n + 1 + k = n + (1 + k) from by ac_rfl] at hk
    simp_all
  simp_all

theorem MyNat.le_antisymm (h₁ : n ≤ m) (h₂ : m ≤ n) : n = m := by
  induction h₁ with
  | refl => rfl
  | @step m h ih =>
    -- h : n ≤ m
    -- ih : m ≤ n → n = m
    have : n < n := calc
      _ ≤ m := by exact h
      _ < m + 1 := by notation_simp; rfl -- この ; はタクティク結合子。順に実行する
      _ ≤ n := by exact h₂
    simp at this

-- calcなしバージョン の練習
example (h₁ : n ≤ m) (h₂ : m ≤ n) : n = m := by
  induction h₁ with
  | refl => rfl
  | @step m h ih =>
    -- h : n ≤ m
    -- ih : m ≤ n → n = m
    -- から矛盾を導く
    have h_lt : n + 1 ≤ m + 1 := MyNat.add_le_add_right h 1
    -- n < m + 1 と m + 1 ≤ n から推移律で n < n を導く
    -- 記述されているルールそのものは n + 1 ≤ n を導くが
    -- n < n := n + 1 ≤ n という定義から自動的に満たされる。
    have h_contra : n < n := MyNat.le_trans h_lt h₂
    -- have は「中身（定義）」を見て判断する一方、simp は「見た目（構文）」を見て判断する
    -- このため have の時点で n < n にしないと失敗する
    simp at h_contra

-- induction なしバージョン の練習
example (h₁ : n ≤ m) (h₂ : m ≤ n) : n = m := by
  rw [MyNat.le_iff_add] at *
  obtain ⟨k1, hk1⟩ := h₁
  obtain ⟨k2, hk2⟩ := h₂
  -- hk1 : n + k1 = m
  -- hk2 : m + k2 = n
  have h3 : m + k2 + k1 = m := by
    rw [hk2]
    exact hk1
  have : k1 = 0 := by
    rw [show m + k2 + k1 = m + (k2 + k1) from by ac_rfl] at h3
    -- h3 : m + (k2 + k1) = m
    simp at h3
    -- h3 : k2 = 0 ∧ k1 = 0 になった。m のキャンセルだけでなく
    exact h3.right
  simp_all -- hk1 と this の組み合わせで解決

-- 練習問題
example (a b : MyNat) : a < b ∨ a = b → a ≤ b := by
  intro h
  cases h
  case inl hlt => -- a < b
    exact MyNat.le_of_lt hlt
  case inr heq => -- a = b
    rw [heq]
