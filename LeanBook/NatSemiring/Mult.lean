import LeanBook.NatCommMonoid.BetterInduction

/-- MyNat についての掛け算 -/
def MyNat.mul (m n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => MyNat.mul m n + m

/-- MyNat の掛け算を * で表せるように 型クラス Mul のインスタンスにする -/
instance : Mul MyNat where
  mul := MyNat.mul

#eval 2 * 3
#eval 3 * 5

/-- 右のオペランドにある (· + 1) の消去 -/
theorem MyNat.mul_add_one (m n : MyNat) : m * (n + 1) = m * n + m := by
  -- MyNat.mul の n + 1 => MyNat.mul m n + m を展開するだけで一致する
  rfl

/-- 左のオペランドにある (· + 1) の消去 -/
theorem MyNat.add_one_mul (m n : MyNat) : (m + 1) * n = m * n + n := by
  induction n with
  | zero => rfl
  | succ n ih => calc
    _ = (m + 1) * (n + 1) := by rfl -- succ n の場合の初期状態の左辺
    _ = (m + 1) * n + (m + 1) := by rw [MyNat.mul_add_one]
    _ = m * n + n + (m + 1) := by rw[ih] -- 帰納法の仮定
    _ = m * n + m + (n + 1) := by ac_rfl -- 足し算の交換法則と結合法則の適用
    _ = m * (n + 1) + (n + 1) := by rfl

/-- 右から 0 を掛けると 0 -/
@[simp] theorem MyNat.mul_zero (m : MyNat) : m * 0 = 0 := by
  rfl

/-- 左から 0 を掛けると 0 -/
@[simp] theorem MyNat.zero_mul (n : MyNat) : 0 * n = 0 := by
  induction n with
  | zero => rfl
  -- 帰納ステップ: n = succ n' (すなわち n = n' + 1) のとき。
  -- ih : 0 * n' = 0 という仮定を用いて、0 * (n' + 1) = 0 を導く。
  -- InfoView に出る ih を証明したい 0 * n = 0 に一致させるため n と置いて変数 n は shadowing している。n' と書いても証明は成功する
  -- n と書いた方が 「任意の n という普遍性」を表現している、ともとれる
  | succ n ih =>
    simp[MyNat.mul_add_one] -- -- 0 * (n' + 1) を 0 * n' + 0 にす
    simp[ih]

-- calc 中の simp は適用 theorem を明示しなくても Lean が自動適用してくれるが使っているものを明示しながら進める
/-- 右から 1 を掛けても変わらない -/
@[simp] theorem MyNat.mul_one (n : MyNat) : n * 1 = n := calc
  _ = n * 1 := by rfl -- 最後まで書ききるとこの行がなくても証明に成功するが、順番に書いている時にこの行がないと 次の行の時点で simp を適用できない
  _ = n * (0 + 1) := by simp[MyNat.zero_add]
  _ = n * 0 + n := by rw[MyNat.mul_add_one]
  _ = n := by simp[mul_zero, zero_add]

private theorem MyNat.mul_one_rfl (n : MyNat) : n * 1 = n := calc
  -- 初手 rfl ならいける
  _ = n * (0 + 1) := rfl
  _ = n * 0 + n := by rw[MyNat.mul_add_one]
  _ = n := by simp[mul_zero, zero_add]

/-- 左から 1 を掛けても変わらない -/
@[simp] theorem MyNat.one_mul (n : MyNat) : 1 * n = n := calc
  _ = 1 * n := by rfl -- 最後まで書ききるとこの行がなくても証明に成功するが、順番に書いている時にこの行がないと 次の行の時点で simp を適用できない
  _ = (0 + 1) * n := by simp[MyNat.zero_add]
  _ = 0 * n + n := by rw[MyNat.add_one_mul]
  _ = n := by simp[zero_mul, zero_add]

private theorem MyNat.one_mul_rfl (n : MyNat) : 1 * n = n := calc
  -- 初手 rfl ならいける
  _ = (0 + 1) * n := by rfl
  _ = 0 * n + n := by rw[MyNat.add_one_mul]
  _ = n := by simp[zero_mul, zero_add]

/-- 掛け算の交換法則 -/
theorem MyNat.mul_comm (m n : MyNat) : m * n = n * m := by
  induction n with
  | zero => simp[mul_zero, zero_mul]
  | succ n ih => calc
    _ = m * (n + 1) := by rfl
    _ = m * n + m := by rw[MyNat.mul_add_one]
    _ = n * m + m := by rw[ih] -- 帰納法の仮定を使う
    _ = (n + 1) * m := by rw[← MyNat.add_one_mul]

/-- 右から掛けた時の分配法則 -/
theorem MyNat.add_mul (l m n : MyNat) : (l + m) * n = l * n + m * n := by
  induction n with
  | zero => rfl
  | succ n ih => calc
    -- ⊢ (l + m) * (n + 1) = l * (n + 1) + m * (n + 1)
    _ = (l + m) * (n + 1) := by rfl -- 最初の左辺
    _ = (l + m) * n + (l + m) := by rw[MyNat.mul_add_one]
    _ = l * n + m * n + (l + m) := by rw[ih]
    _ = (l * n + l) + (m * n + m) := by ac_rfl -- 足し算の交換法則・結合法則
    _ = l * (n + 1) + m * (n + 1) := by simp[← MyNat.mul_add_one]

theorem MyNat.mul_add (l m n : MyNat) : l * (m + n) = l * m + l * n := calc
  -- 掛け算の可換性は示したので、右からの分配法則に帰着させる
  _ = l * (m + n) := by rfl
  _ = (m + n) * l := by simp[MyNat.mul_comm]
  _ = m * l + n * l := by rw[MyNat.add_mul]
  _ = l * m + l * n := by simp[MyNat.mul_comm]

/-- 掛け算の結合法則 -/
theorem MyNat.mul_assoc (l m n : MyNat) : l * m * n = l * (m * n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [MyNat.mul_add, ih]

-- 掛け算の結合法則を登録する
instance : Std.Associative (α := MyNat) (· * ·) where
  assoc := MyNat.mul_assoc

-- 掛け算の交換法則を登録する
instance : Std.Commutative (α := MyNat) (· * ·) where
  comm := MyNat.mul_comm

-- 練習問題
example (m n : MyNat) : m * n * n * m = m * m * n * n := by
  ac_rfl

example (m n : MyNat) : (m + n) * (m + n) = m * m + 2 * m * n + n * n := by
  calc
  _ = (m + n) * (m + n) := by rfl
  _ = (m + n) * m + (m + n) * n := by simp[MyNat.mul_add]
  _ = (m * m + n * m) + (m * n + n * n) := by simp[MyNat.add_mul]
  _ = m * m + (m * n + m * n) + n * n := by ac_rfl
  _ = m * m + (1 * (m * n) + (m * n)) + n * n := by rw[MyNat.one_mul]
  _ = m * m + ((1 + 1) * (m * n)) + n * n := by rw[MyNat.add_one_mul]
  -- 以下2行は by ac_rfl でいける
  _ = m * m + 2 * (m * n) + n * n := by rfl
  _ = m * m + 2 * m * n + n * n := by rw[MyNat.mul_assoc]
