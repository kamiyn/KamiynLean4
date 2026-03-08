import LeanBook.NatSemiring.Distrib

-- Leanで inductive により定義した型（帰納型）が自動的に満たしている性質
-- injection を以下の2つの性質を 証明の文脈へ引き出す
-- 構築の直交性（Disjointness）succ n ≠ zero
-- 構築の単射性（Injectivity）succ m = succ n

/-- MyNat の書くコンストラクタの像は重ならない -/
example (n : MyNat) : MyNat.succ n ≠ MyNat.zero := by
  intro h
  injection h

/-- MyNat のコンストラクタは単射 -/
example ( m n : MyNat) (h : MyNat.succ m = MyNat.succ n) : m = n := by
  injection h

example (m n : MyNat) (h : m + 1 = n + 1) : m = n := by
  injection h

-- 足し算のキャンセル可能性の証明
variable { l m n : MyNat } -- 以降すべて MyNat 型の項とする

/-- 右から足す演算 (· + m) は単射 -/
theorem MyNat.add_right_cancel (h : l + m = n + m) : l = n := by
  induction m
  case zero => simp_all
  case succ m ih =>
    -- ih : l + m = n + m → l = n
    -- h : l + (m + 1) = n + (m + 1)
    -- ⊢ l = n
    have lem : (l + m) + 1 = (n + m) + 1 := calc
      _ = l + (m + 1) := by ac_rfl -- 足し算の結合法則を適用
      _ = n + (m + 1) := by rw [h]
      _ = (n + m) + 1 := by ac_rfl

    have : l + m = n + m := by
      -- (h : m + 1 = n + 1) : m = n の性質を適用
      injection lem

    exact ih this

theorem MyNat.add_left_cancel (h : l + m = l + n) : m = n := by
  -- 交換法則を使って add_right_cancel に帰着させる
  rw [MyNat.add_comm l m, MyNat.add_comm l n] at h
  apply MyNat.add_right_cancel h

section
  -- ここだけの simp 補題として登録する
  attribute [local simp] MyNat.add_left_cancel
  example : l + m = l + n → m = n := by
    simp -- 登録したはずだが simp に無視されている
end -- section

-- 命題をより簡単な命題に置き換えさせたい時は 同値性 ↔ を使って定理を述べる
-- simp は既定では部分式から順に単純化する。simp ↓ は部分式よりも先に単純化を試みる
/-- 右からの足し算のキャンセル -/
@[simp ↓] theorem MyNat.add_right_cancel_iff : l + m = n + m ↔ l = n := by
  constructor
  · apply MyNat.add_right_cancel
  · intro h
    rw [h]

@[simp ↓] theorem MyNat.add_left_cancel_iff : l + m = l + n ↔ m = n := by
  constructor
  · apply MyNat.add_left_cancel
  · intro h
    rw [h]

example : l + m = l + n → m = n := by
  simp

@[simp] theorem MyNat.add_right_eq_self : m + n = m ↔ n = 0 := by
  constructor
  · -- 左から右 m + n = m → n = 0
    -- これは 足し算がキャンセル可能であることから従う
    intro h -- m + n = m を導入する
    have : m + n = m + 0 := by
      rw [h]
      simp
    simp_all
  · -- 右から左 n = 0 → m + n = m
    simp_all

@[simp] theorem MyNat.add_left_eq_self : n + m = m ↔ n = 0 := by
  rw [MyNat.add_comm n m, MyNat.add_right_eq_self] -- 可換性から従う

@[simp] theorem MyNat.self_eq_add_right : m = m + n ↔ n = 0 := by
  rw [show (m = m + n) ↔ (m + n = m) from by exact eq_comm]
  exact add_right_eq_self

@[simp] theorem MyNat.self_eq_add_left : m = n + m ↔ n = 0 := by
  rw [MyNat.add_comm n m, MyNat.self_eq_add_right] -- 可換性から従う

-- 掛け算
/-- 和がゼロなら両方がゼロ -/
theorem MyNat.eq_zero_of_add_eq_zero : m + n = 0 → m = 0 ∧ n = 0 := by
  intro h
  induction n with
  | zero => simp_all
  | succ n ih =>
    -- 矛盾を示す
    exfalso
    rw [show m + (n + 1) = m + n + 1 from by ac_rfl] at h
    injection h -- (m + n) + 1 = 0 が矛盾する

theorem MyNat.add_eq_zero_of_eq_zero : m = 0 ∧ n = 0 → m + n = 0 := by
  intro h
  simp_all

/-- 和がゼロであることと両方がゼロであることは同値 -/
@[simp] theorem MyNat.add_eq_zero_iff_eq_zero : m + n = 0 ↔ m = 0 ∧ n = 0 := by
  exact ⟨MyNat.eq_zero_of_add_eq_zero, MyNat.add_eq_zero_of_eq_zero⟩

@[simp] theorem MyNat.mul_eq_zero (m n : MyNat) : m * n = 0 ↔ m = 0 ∨ n = 0 := by
  constructor
  · -- 左から右 ⊢ m * n = 0 → m = 0 ∨ n = 0
    intro h -- m * n = 0
    induction n with
    | zero =>
      -- simp_all でいけるが練習のため内部を分離してみる
      right -- 0 = 0 を取り出し
      rfl
    | succ n _ =>
      -- h : m * (n + 1) = 0
      -- ⊢ m = 0 ∨ n + 1 = 0
      -- n ≠ 0 の時は m = 0 ないといけない
      left -- m = 0 を Goal にする
      have : m * n + m = 0 := calc
        _ = m * (n + 1) := by distrib
        _ = 0 := by rw [h]
      -- m * n + m = 0 なので m * n = 0 かつ m = 0 が得られる
      simp_all only [add_eq_zero_iff_eq_zero]
  · -- 右から左 ⊢ m = 0 ∨ n = 0 → m * n = 0
    intro h -- h : m = 0 ∨ n = 0
    cases h <;> simp_all -- ∨ の両方のケースとも ⊢ m * n = 0 は明らか

-- 練習問題
example (n m : MyNat) : n + (1 + m) = n + 2 → m = 1 := by
  expand_num -- 2 を展開
  simp_all
