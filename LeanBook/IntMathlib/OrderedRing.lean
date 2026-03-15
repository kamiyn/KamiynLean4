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
theorem MyInt.le.dest (h : a < b) : ∃ k : MyNat, a + (↑ k + 1) = b := by
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
