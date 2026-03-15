import LeanBook.IntMathlib.LinearOrder

-- 環 Ring は以下を満たすもの
--    X は (· + ·) に関して可換群である
--    - 結合法則
--    - 単位元が存在
--    - 逆元が存在 逆元はしばしば -x と書かれる
--    - 交換法則
--    X は (· × ·) に関してモノイドである
--    - 結合法則
--    - 単位元が存在
--    - (逆元の存在 と 交換法則 を **要請しない**)
--    (· + ·) と (· × ·) の間に分配法則が成り立つ
--    - ∀ x y z : X, x × (y + z) = x × y + x × z
--    - ∀ x y z : X, (x + y) × z = x × z + y × z

-- https://github.com/LambdaNote/errata-leanbook-1-1/issues/178
-- さらに全順序 X 上の (· ≤ ·) が定義されていて、環としての2つの演算 (· + ·) , (· × ·) と整合的であるとき
-- (X, +, ×, ≤) は 順序環 を成す
--     (· + ·) は順序を保つ。 ∀ x y z : X, x ≤ y ⇒ x + z ≤ y + z が成り立つ
--     (· × ·) は順序を保つ。 ∀ x y z : 0 ≤ x ∧ 0 ≤ y ⇒ 0 ≤ x × y が成り立つ
-- 前者について
-- https://github.com/LambdaNote/errata-leanbook-1-1/issues/169
-- 169ページの解説には 整合的 について 左からの演算・右からの演算 の両方が示されている
-- コードとしては記述されていないが「整合的」
--
-- 後者の解説 (右からの乗法 xz ≤ yz と同値)
-- MyInt.sub_nonneg x ≤ y ↔ 0 ≤ y - x
-- 両辺に 0 ≤ z を掛け合わせることで 0 ≤ (y - x)z
-- 分配法則により 0 ≤ yz - xz
-- すなわち xz ≤ yz が導かれる。

-- Geminiの見解:
-- 全順序 を要請するのなら「全順序環（Totally Ordered Ring）」ではないか？

variable {a b c : MyInt}

/-- 狭義順序 < を足し算の等式に変形する -/
theorem MyInt.lt.dest (h : a < b) : ∃ k : MyNat, a + (↑ k + 1) = b := by
  notation_simp at h
  obtain ⟨⟨k, hk⟩, h⟩ := h
  -- h : ¬∃ k, b + ↑k = a
  -- hk : a + ↑k = b
  induction k with
  | zero =>
    -- h : ¬∃ k, b + ↑k = a
    -- hk : a + ↑0 = b
    -- ⊢ ∃ k, a + (↑k + 1) = b
    exfalso -- 矛盾を示す
    replace hk : a = b := by simp_all
    have : ∃ k : MyNat, b + ↑ k = a := by
      rw [hk]
      exists 0
      simp
    contradiction
  | succ k _ =>
    -- hk : a + ↑(k + 1) = b
    -- ⊢ ∃ k, a + (↑k + 1) = b
    push_cast at hk
    exists k
    -- hk と goal が一致

theorem MyInt.le.intro (a : MyInt) (b : MyNat) : a ≤ a + ↑ b := by
  exists b

theorem MyInt.lt.intro (h : ∃ k : MyNat, a + (k + 1) = b) : a < b := by
  obtain ⟨k, hk⟩ := h
  simp only [lt_def]
  -- hk : a + (↑k + 1) = b
  -- ⊢ a ≤ b ∧ ¬b ≤ a
  constructor
  case left => -- ⊢ a ≤ b
    notation_simp -- ⊢ ∃ k, a + ↑k = b 和の等式に置き換える
    exists k + 1
  case right => -- ⊢ ¬b ≤ a
    notation_simp -- ⊢ ¬∃ k, b + ↑k = a
    intro ⟨s, hs⟩ -- goal を (∃ k, b + ↑k = a) → False とみなして
    rw [← hs] at hk -- hk : b + ↑s + (↑k + 1) = b
    have : ↑(s + k) + (1 : MyInt) = 0 := calc
      _ = (↑s + ↑k) + (1 : MyInt) := by push_cast; rfl
      _ = (b + ↑s + (↑k + 1)) - b := by abel
      _ = b - b := by rw [hk]
      _ = 0 := by abel

    replace : (0 : MyInt) > 0 := calc
      _ = ↑(s + k) + (1 : MyInt) := by rw [this]
      _ = (1 : MyInt) + ↑(s + k) := by ac_rfl
      _ ≥ (1 : MyInt) := by apply MyInt.le.intro
      _ > (0 : MyInt) := by decide

    contradiction

theorem MyInt.lt_iff_add : a < b ↔ ∃ k : MyNat, a + (k + 1) = b := by
  constructor
  case mp => exact MyInt.lt.dest
  case mpr => exact MyInt.lt.intro

-- 掛け算が正数を保つことの証明
@[push_cast]
theorem MyInt.ofMyNat_mul (m n : MyNat)
    : ↑ (m * n) = (m : MyInt) * (n : MyInt) := by
  dsimp [MyInt.ofMyNat] -- ⊢ ⟦(m * n, 0)⟧ = ⟦(m, 0)⟧ * ⟦(n, 0)⟧
  apply Quotient.sound -- ⊢ (m * n, 0) ≈ (m * n + 0 * 0, m * 0 + n * 0)
  notation_simp
  ring

/-- 正の整数の掛け算は再び正 -/
theorem MyInt.mul_pos (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  rw [MyInt.lt_iff_add] at *
  -- ha : ∃ k, 0 + (↑k + 1) = a
  -- hb : ∃ k, 0 + (↑k + 1) = b
  -- ⊢ ∃ k, 0 + (↑k + 1) = a * b
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  -- hc : 0 + (↑c + 1) = a
  -- hd : 0 + (↑d + 1) = b
  rw [← hc, ← hd]
  -- ⊢ ∃ k, 0 + (↑k + 1) = (0 + (↑c + 1)) * (0 + (↑d + 1))
  exists c * d + c + d
  -- ⊢ 0 + (↑(c * d + c + d) + 1) = (0 + (↑c + 1)) * (0 + (↑d + 1))
  push_cast
  -- ⊢ 0 + (↑c * ↑d + ↑c + ↑d + 1) = (0 + (↑c + 1)) * (0 + (↑d + 1))
  ring

/-- 掛け算が狭義順序を保つ -/
theorem MyInt.sub_pos : 0 < a - b ↔ b < a := by
  constructor <;> intro h
  · --
    -- h : 0 < a - b
    -- ⊢ b < a
    rw [MyInt.lt_iff_add] at *
    -- h : ∃ k, 0 + (↑k + 1) = a - b
    -- ⊢ ∃ k, b + (↑k + 1) = a
    obtain ⟨k, hk⟩ := h
    simp at hk -- hk : ↑k + 1 = a + -b
    exists k
    rw [hk] -- ⊢ b + (a + -b) = a
    abel -- 0 = 0 に簡約される
  · --
    -- h : b < a
    -- ⊢ 0 < a - b
    rw [MyInt.lt_iff_add] at *
    -- h : ∃ k, b + (↑k + 1) = a
    -- ⊢ ∃ k, 0 + (↑k + 1) = a - b
    obtain ⟨k, hk⟩ := h
    exists k
    rw [← hk]
    -- ⊢ 0 + (↑k + 1) = b + (↑k + 1) - b
    abel

theorem MyInt.mul_lt_mul_of_pos_left (h : a < b) (pos : 0 < c)
    : c * a < c * b := by
  suffices 0 < c * (b - a) from by
    -- this : 0 < c * (b - a) suffices の引数が this に入る
    rw [MyInt.lt_iff_add] at this ⊢
    -- this : ∃ k, 0 + (↑k + 1) = c * (b - a)
    -- ⊢ ∃ k, c * a + (↑k + 1) = c * b
    obtain ⟨k, hk⟩ := this
    simp at hk
    -- hk : ↑k + 1 = c * (b + -a)
    use k
    rw [hk]
    -- ⊢ c * a + c * (b + -a) = c * b
    simp [MyInt.left_distrib]
  replace h : 0 < b - a := by
    rw [MyInt.sub_pos]
    assumption
  apply MyInt.mul_pos (ha := pos) (hb := h)

theorem MyInt.mul_lt_mul_of_pos_right (h : a < b) (pos : 0 < c)
    : a * c < b * c := by
  rw [MyInt.mul_comm a c, MyInt.mul_comm b c]
  -- ⊢ c * a < c * b
  apply MyInt.mul_lt_mul_of_pos_left (h := h) (pos := pos)

instance : IsStrictOrderedRing MyInt where
  zero_le_one := by decide
  exists_pair_ne := by
    exists (0 : MyInt), (1 : MyInt)
    decide
  mul_lt_mul_of_pos_left := by apply MyInt.mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := by apply MyInt.mul_lt_mul_of_pos_right

-- CommRing, LinearOrder, IsStrictOrderedRing のインスタンスでは
-- linarith というタクティクが使える

example (a b c : MyInt) (h : a < b) : a + c < b + c := by
  linarith

example (a b : MyInt) (h1 : 2 * a - b = 1) (h2 : a + b = 5) : a =2 := by
  -- 連立方程式も解いてくれる
  linarith

-- IsStrictOrderedRing のインスタンスでは linarith という強力なプロンプトが筒返す
-- linear.libnarith

/-- 左からの掛け算は広義順序を保つ -/
theorem MyInt.mul_le_mul_of_nonneg_left (h : a ≤ b) (mneg : 0 ≤ c)
    : c * a ≤ c * b := by
  nlinarith

/-- 右からの掛け算は広義順序を保つ -/
theorem MyInt.mul_le_mul_of_nonneg_right (h : a ≤ b) (mneg : 0 ≤ c)
    : a * c ≤ b * c := by
  nlinarith

instance : IsOrderedRing MyInt where
  zero_le_one := by decide
  mul_le_mul_of_nonneg_left := by apply MyInt.mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right := by apply MyInt.mul_le_mul_of_nonneg_right

-- 練習問題
example (a b : MyInt) (h1 : 3 * a - 2 * b = 5) (h2 : 6 * a - 5 * b = 11)
    : b = -1 := by
  linarith
