import LeanBook.IntMathlib.DecidableOrd

-- 全順序 total order もしくは linear order
--   X は (· ≤ ·) に関して半順序集合である
--   ∀ x, y ∈ X, x ≤ y ∨ y ≤ x
-- Mathlib の LinearOrder 型クラスは 順序が 決定可能であることを要求する

-- a ≤ b ∨ b ≤ a を
-- 0 ≤ (a - b) ∨ 0 ≤ -(a - b) と書き換えれば
-- 0 ≤ a       ∨ 0 ≤ -a を示せば十分

theorem MyInt.nonneg_or_nonneg_neg {a : MyInt} : 0 ≤ a ∨ 0 ≤ -a := by
  -- a : MyInt の代表元 を取る
  induction a using Quotient.inductionOn with
  | h a => -- ⊢ 0 ≤ ⟦a⟧ ∨ 0 ≤ -⟦a⟧ ここで a は PreInt
    obtain ⟨m, n⟩ := a -- m, n は 自然数 MyNat
    -- ⊢ 0 ≤ ⟦(m, n)⟧ ∨ 0 ≤ -⟦(m, n)⟧

    have : n ≤ m ∨ m ≤ n := by
      -- 自然数については全順序がすでに示せている
      exact MyNat.le_total n m
    cases this with
    | inl h => -- h : n ≤ m
      left
      simp [mk_def]
      -- goal: 0 ≤ (m : MyInt) - (n : MyInt)
      rw [MyInt.sub_nonneg]
      -- goal: (n : MyInt) ≤ (m : MyInt)
      exact (by exact_mod_cast h)
    | inr h => -- h : m ≤ n
      right
      simp [mk_def]
      -- goal: 0 ≤ (n : MyInt) - (m : MyInt)
      rw [MyInt.sub_nonneg]
      -- goal: (m : MyInt) ≤ (n : MyInt)
      exact (by exact_mod_cast h)

/-- 整数は全順序 -/
theorem MyInt.le_total (a b : MyInt) : a ≤ b ∨ b ≤ a := by
  suffices goal : 0 ≤ b - a ∨ 0 ≤ -(b - a) from by
    cases goal with
    | inl h =>
      left
      rw [← MyInt.sub_nonneg]
      assumption
    | inr h =>
      right
      rw [← MyInt.sub_nonneg]
      rw [show -(b - a) = a - b from by abel] at h
      assumption
  exact nonneg_or_nonneg_neg

instance : LinearOrder MyInt where
  toDecidableLE := by infer_instance
  le_total := by exact MyInt.le_total

theorem MyInt.eq_or_lt_of_le {a b : MyInt} (h : a ≤ b) : a = b ∨ a < b := by
  by_cases hor : a = b
  case pos => -- hor : a = b
    left
    exact hor
  case neg => -- hor : ¬ a = b
    right
    order -- h と hor を結合すると a < b になる

theorem MyInt.le_of_eq_or_lt {a b : MyInt} (h : a = b ∨ a < b) : a ≤ b := by
  cases h with
  | inl h => rw [h]
  | inr h => order

theorem MyInt.le_iff_eq_or_lt (m n : MyInt) : n ≤ m ↔ n = m ∨ n < m := by
  constructor
  case mp => apply MyInt.eq_or_lt_of_le
  case mpr => apply MyInt.le_of_eq_or_lt

-- 練習問題
-- https://github.com/LambdaNote/errata-leanbook-1-1/issues/207
-- 1問めの解答が207ページにない
example {a b : MyInt} (h : b < a) : ¬ a ≤ b := by
  have : b ≤ a ∧ ¬ (a ≤ b) := by
    dsimp [(· < ·), MyInt.lt] at h
    exact h
  exact this.right

example {a : MyInt} (neg : a ≤ 0) : 0 ≤ -a := by
  have : 0 + a ≤ -a + a := calc
    _ = a := by abel
    _ ≤ 0 := by simp_all
    _ = -a + a := by abel
  simp_all

example {a : MyInt} (neg : a ≤ 0) : 0 ≤ -a := by
  notation_simp at *
  -- neg : ∃ k, a + ↑k = 0
  -- ⊢ ∃ k, 0 + ↑k = -a
  obtain ⟨k, hk⟩ := neg
  have : ↑k = -a := calc
    _ = (a + ↑k) - a := by abel
    _ = 0 - a := by rw [hk]
    _ = - a := by simp
  exists k
  simp_all
