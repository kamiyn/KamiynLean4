import LeanBook.IntMathlib.PartialOrder

-- 順序群があったとして整合的であるとは
-- ∀ x,y,z ∈ X, x ≤ y → x ⋄ z ≤ y ⋄ z -- 右から z を適用
-- ∀ x,y,z ∈ X, x ≤ y → z ⋄ x ≤ z ⋄ y -- 左から z を適用
-- このファイルでは 左からの加法 のみを扱っている

-- GitHub Copilot 指摘事項
-- ファイル名/章タイトルが「OrderedAddCommGroup（順序群）」ですが、ここで登録しているのは IsOrderedAddMonoid MyInt（モノイドの順序整合性）だけ
-- 本の分量 との兼ね合いで削られた可能性がある

theorem MyInt.add_le_add_left (a b : MyInt) (h : a ≤ b) (c : MyInt)
    : c + a ≤ c + b := by
  notation_simp at *
  obtain ⟨m, hm⟩ := h
  -- hm : a + ↑m = b
  -- ⊢ ∃ k, c + a + ↑k = c + b
  exists m -- ここで k = m とすればよい
  have : c + a + ↑ m = c + b := calc
    _ = c + (a + ↑ m) := by ac_rfl
    _ = c + b := by rw [hm]
  assumption

instance : IsOrderedAddMonoid MyInt where
  add_le_add_left := MyInt.add_le_add_left

-- 練習問題
example {a : MyInt} (nneg : 0 ≤ a) : ∃ k : MyNat, a = ↑ k := by
  notation_simp at *
  obtain ⟨k, hk⟩ := nneg
  exists k
  -- hk : 0 + ↑k = a
  -- ⊢ a = ↑k
  simp_all
