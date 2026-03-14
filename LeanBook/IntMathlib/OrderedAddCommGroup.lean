import LeanBook.IntMathlib.PartialOrder

-- 順序群があったとして整合的であるとは
-- ∀ x,y,z ∈ X, x ≤ y → x ⋄ z ≤ y ⋄ z -- 後ろから z を適用
-- ∀ x,y,z ∈ X, x ≤ y → z ⋄ x ≤ z ⋄ y -- 前から z を適用

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
