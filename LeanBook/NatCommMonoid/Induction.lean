import LeanBook.NatCommMonoid.TypeClass

-- example (n: MyNat) : 0 + n = n := by
--   rfl
-- tactic 'rfl' failed, the left-hand side
--   0 + n
-- is not definitionally equal to the right-hand side
--   n

#reduce fun (n : MyNat) => n + 0
#reduce fun (n : MyNat) => 0 + n

-- rwタクティクで等式置換 (本では後から出現する)
/-- 0 を右から足しても変わらない -/
theorem MyNat.add_zero (n : MyNat) : n + 0 = n := by rfl
example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [MyNat.add_zero]

/-- 0 を右から足しても変わらない 等式の順序が逆バージョン -/
theorem MyNat.add_zero_rev (n : MyNat) : n = n + 0 := by rfl
example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [← MyNat.add_zero_rev]

-- ローカルコンテキストにある仮定を at を利用して書き換え
example (m n : MyNat) (h : m + 0 = n) : n + m = m + n := by
  -- 仮定の h を簡略化して m = n を得る。 h が m = n に変化する
  rw [MyNat.add_zero] at h
  rw [h]

theorem MyNat.add_succ (m n : MyNat) : m + MyNat.succ n = MyNat.succ (m + n) := by rfl

set_option pp.fieldNotation.generalized false in

/-- 0 を左から足しても変わらない -/
theorem MyNat.zero_add (n : MyNat) : 0 + n = n := by
  -- n についての帰納法で証明する
  induction n with
  -- MyNat のコンストラクタが zero と succ (n : MyNat) なので、それらでパターン分けする
  | zero =>
    -- ゴールが ⊢ 0 + MyNat.zero = MyNat.zero という形になる
    guard_target =ₛ 0 + MyNat.zero = MyNat.zero
    -- 変数がないのでrflで証明できる
    rfl
  -- n = succ n' のケース
  | succ n' ih =>
    -- ゴールが ⊢ 0 + MyNat.succ n' = MyNat.succ n'
    guard_target =ₛ 0 + MyNat.succ n' = MyNat.succ n'
    -- 帰納法の仮定 ih (等式) が手に入る
    guard_hyp ih : 0 + n' = n'
    -- 0 + MyNat.succ n' を変形し外側に .succ をもってくる
    rw[MyNat.add_succ]
    -- ⊢ MyNat.succ (0 + n') = MyNat.succ n'
    rw[ih]

-- induction n with と | の記法他に induction n と case の書き方もある
-- case の書き方の方が C# に近い
example (n : MyNat) : 0 + n = n := by
  induction n
  case zero =>
    rfl
  case succ n' ih =>
    rw[MyNat.add_succ]
    rw[ih]

-- 練習問題
example (n : MyNat) : 1 + n = MyNat.succ n := by
  induction n
  case zero =>
    rfl -- 1 + MyNat.zero
  case succ n' ih =>
    rw[MyNat.add_succ]
    rw[ih]

-- 等式の等価性（Congruence） を利用
-- a = b から f(a) = f(b) をを導出
-- Lean（および純粋関数型言語）において、すべての関数は数学的な意味での関数、すなわち「同じ入力に対しては常に同じ出力を返す」決定的な存在
-- congrArg の利用は 非依存型なら型エラーの余地がない とのこと
example (n : MyNat) : 0 + n = n := by
  induction n
  case zero =>
    rfl
  case succ n' ih =>
    -- ゴール ⊢ 0 + MyNat.succ n' = MyNat.succ n' は、
    -- 定義により ⊢ MyNat.succ (0 + n') = MyNat.succ n' と定義的に等しい。
    -- ここで、ih : 0 + n' = n' の両辺に MyNat.succ を適用する。
    exact congrArg MyNat.succ ih
