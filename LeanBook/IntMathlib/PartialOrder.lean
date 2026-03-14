import LeanBook.IntMathlib.PreOrder

-- 半順序 (partial order) であるとは
--   X は ≤ に関して前順序集合である
--   ≤ は反対称性を満たす : ∀ x,y ∈ X, x ≤ y ∧ ¥ ≤ x ⇒ x = y

@[simp ↓]
theorem MyInt.add_right_eq_self {a b : MyInt} : a + b = a ↔ b = 0 := by
  constructor <;> intro h
  case mp => -- ⊢ b = 0
    -- h : a + b = a
    -- 整数 MyInt が Abel群であることと仮定から計算して示す
    calc
    _ = b := by rfl -- ⊢ b = 0 の左辺
    _ = a + b - a := by abel -- アーベル群における加法逆元を用いた恒等変形（b = (b + a) - a）と可換性による整理
    _ = a - a := by rw [h] -- 仮定 a + b = a の適用
    _ = 0 := by abel
  case mpr => -- ⊢ a + b = a
    -- h : b = 0
    simp [h]

theorem MyInt.le_antisymm (a b : MyInt) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  notation_simp at * -- 和の等式で展開
  obtain ⟨m, hm⟩ := h1
  obtain ⟨n, hn⟩ := h2
  -- hm : a + ↑m = b
  -- hn : b + ↑n = a
  -- ⊢ a = b
  have : a + (↑m + ↑n) = a := calc
    _ = a + ↑m + ↑n := by ac_rfl
    _ = b + ↑n := by rw [hm]
    _ = a := by rw [hn]
  -- これは 補題より ↑(m + n) = 0 を意味する
  replace : ↑(m + n) = (0 : MyInt) := by
  -- replace は、ほぼ have と同じだが同一名称で宣言した時に上書きする
  -- ここでは無名 have なので have の連鎖でも大丈夫に見える
    push_cast
    simp_all
  have ⟨mz, nz⟩ : m = 0 ∧ n = 0 := by
    -- ⟨mz, nz⟩ なしでも解決してくれるようだ
    -- InfoView 的には m = 0 ∧ n = 0 から m = 0, n = 0 に分解してくれる方が見やすい
    simp_all
  simp_all

instance : PartialOrder MyInt where
  le_antisymm := by apply MyInt.le_antisymm

-- order で利用可能になった
example (a b : MyInt) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  order

-- 練習問題
example (a b : MyInt) (h : a = b ∨ a < b) : a ≤ b := by
  cases h
  case inl hl => -- hl : a = b
    order
    -- https://github.com/LambdaNote/errata-leanbook-1-1/issues/168
    -- 本では rw [hl] 相当の書き方だった
    -- 次の example のように1行化する方が PartialOrder っぽさが表現されているように思える
  case inr hr => -- hr : a < b
    order

-- ということは
example (a b : MyInt) (h : a = b ∨ a < b) : a ≤ b := by
  cases h <;> order
