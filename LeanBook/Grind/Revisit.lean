-- MyNat 再訪

-- 2.2 節と同じ定義
inductive MyNat where
  | zero -- コンストラクタ
  | succ (n : MyNat) -- コンストラクタ

def MyNat.add (m n : MyNat) : MyNat :=
  match n with -- パターンマッチの対象 n
  | .zero => m -- 名前空間 MyNat を省略
  | .succ n => succ (add m n) -- ここの n は パターンマッチの対象 n とスコープが異なる

instance : Add MyNat where
  add := MyNat.add

-- def MyNat.ofNat (n : Nat) : MyNat :=
--   match n with
--   | n => MyNat.zero
--   | n + 1 => MyNat.succ (MyNat.ofNat n)

def MyNat.ofNat (n : Nat) : MyNat :=
  match n with
    | 0 => MyNat.zero
    | n + 1 => MyNat.succ (MyNat.ofNat n)

/-- OfNat のインスタンスを実装する -/
@[default_instance] -- 数値リテラルがLeanの組み込みのNat型の項として解釈されるのを防ぐ
instance (n : Nat) : OfNat MyNat n where
  ofNat := MyNat.ofNat n

@[simp, grind =]
theorem MyNat.zero_eq_zero_lit : MyNat.zero = 0 := by rfl
@[simp, grind =]
theorem MyNat.succ_eq_add_one (n : MyNat) : .succ n = n + 1 := by rfl

/-- MyNat用の帰納法の原理を書き直したもの -/
@[induction_eliminator]
def MyNat.recAux.{u} {motive : MyNat → Sort u}
  (zero : motive 0)
  (succ : (n : MyNat) → motive n → motive (n + 1)) (t : MyNat) : motive t :=
  match t with
  | .zero => zero
  | .succ n => succ n (MyNat.recAux zero succ n)

-- ゼロ加算 を 再定義
@[simp, grind =]
theorem MyNat.add_zero (n : MyNat) : n + 0 = n := by rfl

@[simp, grind =]
theorem MyNat.add_succ (m n : MyNat) : m + .succ n = .succ (m + n) := by rfl

@[grind =]
theorem MyNat.add_add_one (m n : MyNat) : m + (n + 1) = (m + n) + 1 := by rfl

-- 0 を左から足す操作は 当初は大変だった [NatCommMonoid/Induction.lean](../NatCommMonoid/Induction.lean)
@[simp, grind =]
theorem MyNat.zero_add (n : MyNat) : 0 + n = n := by
  induction n with grind

-- 左のオペランドに付いた .succ は外側に出せる
@[simp, grind =]
theorem MyNat.succ_add (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with grind

/-- 左のオペランドに追加 (· + 1) は外側に出せる -/
@[grind =]
theorem MyNat.add_one_add (m n : MyNat) : (m + 1) + n = (m + n) + 1 := by
  induction n with grind

/-- 足し算の交換法則 -/
@[grind _=_]
theorem MyNat.add_comm (m n : MyNat) : m + n = n + m := by
  induction n with grind

/-- 足し算の結合法則 -/
@[grind _=_]
theorem MyNat.add_assoc (l m n: MyNat) : l + m + n = l + (m + n) := by
  induction n with grind

instance : Std.Associative (α := MyNat) (· + ·) where
  assoc := MyNat.add_assoc

instance : Std.Commutative (α := MyNat) (· + ·) where
  comm := MyNat.add_comm

def MyNat.mul (m n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => MyNat.mul m n + m

instance : Mul MyNat where
  mul := MyNat.mul

-- みぎから0を掛けても 0
/-- 掛け算の定義 -/
@[simp, grind =]
theorem MyNat.mul_zero (m : MyNat) : m * 0 = 0 := by rfl

@[grind _=_]
theorem MyNat.mul_add_one (m n: MyNat) : m * (n + 1) = m * n + m := by
  rfl

@[simp, grind =]
theorem MyNat.zero_mul (n : MyNat) : 0 * n = 0 := by
  induction n with grind

@[grind _=_]
theorem MyNat.add_one_mul (m n: MyNat) : (m + 1) * n = m * n + n := by
  induction n with grind

@[simp, grind =]
theorem MyNat.mul_one (n : MyNat) : n * 1 = n := by
  induction n with grind

@[simp, grind =]
theorem MyNat.one_mul (n : MyNat) : 1 * n = n := by
  induction n with grind

@[grind =]
theorem MyNat.mul_comm (m n : MyNat) : m * n = n * m := by
  induction n with grind

@[grind _=_]
theorem MyNat.add_mul (l m n : MyNat) : (l + m) * n = l * n + m * n := by
  induction n with grind

@[grind =]
theorem MyNat.mul_add (l m n : MyNat) : l * (m + n) = l * m + l * n := by
  grind

@[grind _=_]
theorem MyNat.mul_assoc (l m n : MyNat) : l * m * n = l * (m * n) := by
  induction n with grind

instance : Std.Associative (α := MyNat) (· * ·) where
  assoc := MyNat.mul_assoc

instance : Std.Commutative (α := MyNat) (· * ·) where
  comm := MyNat.mul_comm

-- grind 1行で終わらせるためには、補題を見つけ出す必要があるケースが存在するとのこと

-- 練習問題
variable {l m n : MyNat}

/-- 右から足す演算 (· + m) は単射 -/
@[grind →]
theorem MyNat.add_right_cancel (h : l + m = n + m) : l = n := by
  sorry

@[grind →]
theorem MyNat.add_left_cancel (h : l + m = l + n) : m = n := by
  sorry
