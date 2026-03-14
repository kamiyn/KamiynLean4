import LeanBook.IntMathlib.OrderedAddCommGroup

-- 整数の順序関係は決定可能
-- 命題 P : Prop が成り立つかどうか計算するアルゴリズムがある

/-- 商は引き算を意味する ⟦(n₁, n₂)⟧ = ↑n₁ - ↑n₂ -/
theorem MyInt.mk_def (x y : MyNat) : ⟦(x, y)⟧ = (x : MyInt) - (y : MyInt) := by
  simp [ofMyNat] -- 自然数から整数への変換 をすれば MyInt の定義からそのようになる

-- n すなわち (n₁, n₂) において
-- n₂ ≤ n₁ であれば 0 ≤ n という流れで 0 ≤ n を判定するアルゴリズムを構成する
def PreInt.bpos (n : PreInt) : Bool :=
  match n with
  | (n₁, n₂) => decide (n₂ ≤ n₁)

/-- 整数n に対して 0 ≤ n かどうかを判定する関数 -/
def MyInt.bpos : MyInt → Bool := Quotient.lift PreInt.bpos <| by
  -- ⊢ ∀ (a b : PreInt), a ≈ b → a.bpos = b.bpos
  intro (a, b) (c, d) hr
  -- hr : (a, b) ≈ (c, d)
  -- ⊢ PreInt.bpos (a, b) = PreInt.bpos (c, d)
  notation_simp at hr
  -- hr : a + d = b + c
  dsimp [PreInt.bpos]
  -- ⊢ decide (b ≤ a) = decide (d ≤ c)
  suffices b ≤ a ↔ d ≤ c from by
    simp_all

  constructor <;> intro h
  case mp =>
    -- h : b ≤ a
    -- ⊢ d ≤ c
    have : b + d ≤ a + d := by
      simp
      exact h
    rw [hr] at this -- this : b + d ≤ b + c
    simp_all
    -- 本では calc の利用と compatible が登場する
  case mpr =>
    -- h : d ≤ c
    -- ⊢ b ≤ a
    have : a + d ≤ a + c := by
      simp
      exact h
    rw [hr] at this
    simp_all

-- 後で使うので補題として用意しておく
@[simp]
theorem MyInt.bpos_def (m n : MyNat) : MyInt.bpos ⟦(m, n)⟧ = true ↔ n ≤ m := by
  dsimp [MyInt.bpos, PreInt.bpos]
  simp

-- 以下 MyInt.bpos z = true ↔ 0 ≤ z を証明する
/-- 型キャストは順序と整合性がある -/
@[norm_cast]
theorem MyInt.ofMyNat_le (m n : MyNat) : (m : MyInt) ≤ (n : MyInt) ↔ m ≤ n := by
  rw [MyNat.le_iff_add]
  notation_simp
  constructor <;> intro ⟨k, hk⟩
  case mp =>
    -- hk : ↑m + ↑k = ↑n
    -- ⊢ ∃ k, m + k = n
    exists k
    have : ↑ (m + k) = (n : MyInt) := by
      norm_cast at hk
    norm_cast at this
  case mpr =>
    -- hk : m + k = n
    -- ⊢ ∃ k, ↑m + ↑k = ↑n
    exists k
    rw [← hk] -- ⊢ ↑m + ↑k = ↑(m + k)
    norm_cast

theorem MyInt.le_sub_iff (x y z : MyInt) : z ≤ x - y ↔ z + y ≤ x := by
  notation_simp
  constructor <;> intro ⟨k, hk⟩
  case mp =>
    -- hk : z + ↑k = x + -y
    -- ⊢ ∃ k, z + y + ↑k = x
    exists k
    have : z + y + ↑k = x := calc
      _ = z + ↑k + y := by ac_rfl
      _ = x + -y + y := by rw [hk]
      _ = x := by abel
    exact this
  case mpr =>
    -- hk : z + y + ↑k = x
    -- ⊢ ∃ k, z + ↑k = x + -y
    exists k
    have : z + ↑k = x + -y := calc
      _ = (z + y + ↑k) + -y := by abel
      _ = x + -y := by rw [hk]
    exact this

theorem MyInt.sub_nonneg (m n : MyInt) : 0 ≤ m - n ↔ n ≤ m := by
  have := MyInt.le_sub_iff m n 0
  simp_all -- Try this: simp_all only [sub_def, le_add_neg_iff_add_le, _root_.zero_add]

theorem MyInt.bpos_iff (z : MyInt) : MyInt.bpos z = true ↔ 0 ≤ z := by
  induction z using Quotient.inductionOn with
  | h a =>
    -- ⊢ bpos ⟦a⟧ = true ↔ 0 ≤ ⟦a⟧
    -- z = ⟦(x, y)⟧ として代表元 (x, y) を取る
    obtain ⟨x, y⟩ := a
    -- ⊢ bpos ⟦(x, y)⟧ = true ↔ 0 ≤ ⟦(x, y)⟧
    rw [MyInt.bpos_def, MyInt.mk_def]
    rw [MyInt.sub_nonneg]
    -- ⊢ y ≤ x ↔ ↑y ≤ ↑x
    -- 型キャストの性質を使う
    norm_cast

instance : DecidablePred (0 ≤ · : MyInt → Prop) := by
  intro n
  apply decidable_of_iff (MyInt.bpos n = true)
  exact MyInt.bpos_iff n
-- decide タクティクが 0 ≤ n という命題に対して利用できるようになった
example : 0 ≤ (3 : MyInt) := by decide

-- n ≤ m は決定可能
instance : DecidableLE MyInt := by
  intro n m
  apply decidable_of_iff (0 ≤ m - n)
  exact MyInt.sub_nonneg m n

#eval (3 : MyInt) ≤ 4
example : (3 : MyInt) ≤ 4 := by decide

-- 狭義順序を 決定可能にする
instance : DecidableLT MyInt := by
  intro n m
  dsimp [(· < ·), MyInt.lt]
  infer_instance

#eval (3 : MyInt) < 4
example : (3 : MyInt) < 4 := by decide

-- DecidableEq の登録
instance : DecidableEq MyInt := decidableEqOfDecidableLE

#eval (3 : MyInt) = 4
example : ¬ (3 : MyInt) = 4 := by decide

-- 練習問題
/-- 自然数の像は非負の整数である -/
example (a : MyInt) (h : ∃ k : MyNat, a = ↑k) : 0 ≤ a := by
  obtain ⟨k, hk⟩ := h
  -- 和の等式に置き換える
  notation_simp -- Try this: simp only [MyInt.le_def]
  -- ⊢ ∃ k, 0 + ↑k = a
  exists k
  simp_all
