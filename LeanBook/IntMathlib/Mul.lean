import LeanBook.IntMathLib.Add

-- ここから自然数が半環であることを再利用可能にする

/-- 単位元が何であるかを指定する -/
instance : Zero MyNat where
  zero := 0

-- 可換なモノイドとして登録
instance : AddCommMonoid MyNat where
  zero_add := MyNat.zero_add
  add_zero := MyNat.add_zero
  add_assoc := MyNat.add_assoc
  add_comm := MyNat.add_comm
  nsmul := nsmulRec

/-- 掛け算の単位元を指定する -/
instance : One MyNat where
  one := 1

/-- MyNat は可換な半環 -/
instance : CommSemiring MyNat where
  left_distrib := MyNat.mul_add
  right_distrib := MyNat.add_mul
  zero_mul := MyNat.zero_mul
  mul_zero := MyNat.mul_zero
  mul_one := MyNat.mul_one
  one_mul := MyNat.one_mul
  mul_assoc := MyNat.mul_assoc
  mul_comm := MyNat.mul_comm

-- CommSemiring の状態でも ring タクティクは使える
-- この時点では instance: Zero, instance: One が使われていない
example (a b c : MyNat) : (a + b) * (a + c) = a * a + (b + c) * a + b * c := by
  ring

/-- PreInt 上の掛け算 -/
def PreInt.mul (m n : PreInt) : MyInt :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => ⟦(m₁ * n₁ + m₂ * n₂, m₁ * n₂ + n₁ * m₂)⟧

/-- 整数の掛け算 -/
def MyInt.mul : MyInt → MyInt → MyInt := Quotient.lift₂ PreInt.mul <| by
  intro (a, b) (c, d) (p, q) (r, s) h₁ h₂
  -- h₁ : (a, b) ≈ (p, q)
  -- h₂ : (c, d) ≈ (r, s)
  -- ⊢ PreInt.mul (a, b) (c, d) = PreInt.mul (p, q) (r, s)
  dsimp [PreInt.mul]
  -- ⊢ ⟦(a * c + b * d, a * d + c * b)⟧ = ⟦(p * r + q * s, p * s + r * q)⟧
  apply Quotient.sound
  -- ⊢ (a * c + b * d, a * d + c * b) ≈ (p * r + q * s, p * s + r * q)
  notation_simp -- 等式に変換
  -- ⊢ a * c + b * d + (p * s + r * q) = a * d + c * b + (p * r + q * s)
  -- 左辺と右辺をそれぞれ長いので変数におく
  generalize hl : a * c + b * d + (p * s + r * q) = lhs
  generalize hr : a * d + c * b + (p * r + q * s) = rhs

  -- ここから lhs と rhs に q * c を足して同じ式を算出する方針の証明
  have leml : lhs + q * c = c * b + b * d + d * p + p * r + r * q := calc
    _ = a * c + b * d + (p * s + r * q) + q * c := by rw[hl]
    -- このタイミングで 足した q * c のどちらかでまとめればいいだろう とアタリがつく
    _ = (a + q) * c + b * d + p * s + q * r := by ring -- * c をまとめて r * q を交換
    _ = (b + p) * c + b * d + p * s + q * r := by rw [h₁] -- (a + q) を (b + p) に変換
    _ = b * c + b * d + q * r + p * (c + s) := by ring -- p * をまとめる
    _ = b * c + b * d + q * r + p * (d + r) := by rw [h₂] -- (c + s) を (d + r) に変換
    _ = c * b + b * d + d * p + p * r + r * q := by ring

  have lemr : rhs + q * c = c * b + b * d + d * p + p * r + r * q := calc
    _ = a * d + c * b + (p * r + q * s) + q * c := by rw[hr]
    -- leml の初手は * c でまとめたので、lemr は q * でまとめればよさそうである。h₂ の形式に合わせる
    -- rw [h₂], rw [h₁] の適用をするだろうとアタリをつければ自力で進める
    _ = a * d + c * b + p * r + q * (c + s) := by ring
    _ = a * d + c * b + p * r + q * (d + r) := by rw [h₂]
    _ = (a + q) * d + c * b + p * r + q * r := by ring
    _ = (b + p) * d + c * b + p * r + q * r := by rw [h₁]
    _ = c * b + b * d + d * p + p * r + r * q := by ring

  have : lhs + q * c = rhs + q * c := by rw [leml, lemr]
  simp_all -- Try this: simp_all only [↓MyNat.add_right_cancel_iff]

instance : Mul MyInt where
  mul := MyInt.mul

@[notation_simp]
theorem MyNat.toMyNat_one : MyNat.ofNat 1 = 1 := rfl

@[simp]
theorem MyInt.mul_one (m : MyInt) : m * 1 = m := by
  revert m
  unfold_int₁
  ring

@[simp]
theorem MyInt.one_mul (m : MyInt) : 1 * m = m := by
  revert m
  unfold_int₁
  ring

@[simp]
theorem MyInt.mul_zero (m : MyInt) : m * 0 = 0 := by
  revert m
  unfold_int₁
  ring -- https://github.com/LambdaNote/errata-leanbook-1-1/issues/159 この行が抜けている

@[simp]
theorem MyInt.zero_mul (m : MyInt) : 0 * m = 0 := by
  revert m
  unfold_int₁
  ring

theorem MyInt.mul_comm (m n : MyInt) : m * n = n * m := by
  revert m n
  unfold_int₂
  ring

theorem MyInt.mul_assoc (m n k : MyInt) : m * n * k = m * (n * k) := by
  revert m n k
  unfold_int₃
  ring

theorem MyInt.left_distrib (m n k : MyInt) : m * (n + k) = m * n + m * k := by
  revert m n k
  unfold_int₃
  ring

theorem MyInt.right_distrib (m n k : MyInt) : (m + n) * k = m * k + n * k := by
  revert m n k
  unfold_int₃
  ring

-- ring タクティクで再利用可能にする
instance : CommRing MyInt where
  left_distrib := MyInt.left_distrib
  right_distrib := MyInt.right_distrib
  zero_mul := MyInt.zero_mul
  mul_zero := MyInt.mul_zero
  mul_assoc := MyInt.mul_assoc
  one_mul := MyInt.one_mul
  mul_one := MyInt.mul_one
  mul_comm := MyInt.mul_comm
  -- 以下の2つは指定しなくてもエラーにはならないが
  -- **「一貫性を保つために、常に最も基本的な定義（この場合は zsmulRec 等）を明示的に指定する」**のが Lean におけるベストプラクティス (Gemini)
  zsmul := zsmulRec
  neg_add_cancel := MyInt.neg_add_cancel

example (m n : MyInt) : (m - n) * (m + n) = m * m - n * n := by
  ring

-- 練習問題
example (m : MyInt) : ∃ s t : MyInt, s * t = m * m * m - 1 := by
  exists (m * m * m - 1), 1
  -- ⊢ (m * m * m - 1) * 1 = m * m * m - 1
  ring

-- 本の回答。因数分解をしている
example (m : MyInt) : ∃ s t : MyInt, s * t = m * m * m - 1 := by
  use (m * m + m + 1), (m - 1)
  ring
  -- use は Mathlib.Tactic.Use で定義されている拡張機能
  -- use は項を適用した後、自動的に trivial や refl に相当する簡約を試みます。
  -- 代入後、残ったゴールが refl 等で解ければ閉じる
