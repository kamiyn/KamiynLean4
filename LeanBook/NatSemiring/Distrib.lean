import LeanBook.NatSemiring.Mult

example (m n : MyNat) : m * (n + 1) + 2 * (m + n) = m * n + 3 * m + 2 * n := by
  rw [MyNat.mul_add]
  guard_target =ₛ m * n + m * 1 + 2 * (m + n) = m * n + 3 * m + 2 * n
  sorry
  -- rw は渡された等式にマッチする引数の割り当てを1つ見つけると、そこで探索をやめてしまう

example (m n : MyNat) : m * (n + 1) + 2 * (m + n) = m * n + 3 * m + 2 * n := by
  rw [MyNat.mul_add m n 1, MyNat.mul_add 2 m n]
  guard_target =ₛ m * n + m * 1 + (2 * m + 2 * n) = m * n + 3 * m + 2 * n
  sorry

-- 1つの補題を引数を変えながらマッチしてほしい場合は、 simp を使用する
-- guard_target の右辺 は2回適用した直前のものと一致
example (m n : MyNat) : m * (n + 1) + 2 * (m + n) = m * n + 3 * m + 2 * n := by
  simp only [MyNat.mul_add] -- only を指定すると 明示的に列挙した補題だけを使う
  guard_target =ₛ m * n + m * 1 + (2 * m + 2 * n) = m * n + 3 * m + 2 * n
  sorry

-- 足し算を外側に
example (m n : MyNat) : m * (n + 1) + (2 + m) * m = m * n + 3 * m + m * m := by
  simp only [MyNat.mul_add, MyNat.add_mul]
  guard_target =ₛ m * n + m * 1 + (2 * m + m * m) = m * n + 3 * m + m * m
  sorry

-- マクロの定義
macro "distrib" : tactic => `(tactic| simp only [MyNat.mul_add, MyNat.add_mul])

example (m n : MyNat) : m * (n + 1) + (2 + m) * m = m * n + 3 * m + m * m := by
  distrib
  guard_target =ₛ m * n + m * 1 + (2 * m + m * m) = m * n + 3 * m + m * m
  sorry

-- focus というタクティクをマクロ内先頭に配置すると複数のタクティクを1つにまとめる
macro "distrib" : tactic => `(tactic| focus
  simp only [MyNat.mul_add, MyNat.add_mul]
  simp only [MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_one, MyNat.one_mul]
  ac_rfl
)

example (m n : MyNat)
  : m * (n + 1) + (2 + n) * n = m * n + m + 2 * n + n * n := by
  distrib

example (m n : MyNat) : m * (n + 1) + (2 + m) * m = m * n + 3 * m + m * m := by
  simp only [MyNat.mul_add, MyNat.add_mul]
  simp only [MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_one, MyNat.one_mul]
  fail_if_success ac_rfl -- ac_rfl が通らない
  guard_target =ₛ m * n + m + (2 * m + m * m) = m * n + 3 * m + m * m
  sorry

-- 分配法則を適用する前に 数値リテラルを 1+1+...+1 という形に変形すると証明が通る
example (m n : MyNat) : m * (n + 1) + (2 + m) * m = m * n + (3 * m) + (m * m) := by
  rw [show 3 = 1 + 1 + 1 from rfl]
  rw [show 2 = 1 + 1 from rfl]
  simp only [MyNat.mul_add, MyNat.add_mul]
  simp only [MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_one, MyNat.one_mul]
  ac_rfl

macro "distrib" : tactic => `(tactic| focus
  rw [show 3 = 1 + 1 + 1 from rfl]
  rw [show 2 = 1 + 1 from rfl]
  simp only [MyNat.mul_add, MyNat.add_mul]
  simp only [MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_one, MyNat.one_mul]
  ac_rfl
)

example (m n : MyNat) : m * (n + 1) + (2 + m) * m = m * n + (3 * m) + (m * m) := by
  distrib

/-- 数値リテラルを 1 + 1 + ... + 1 に分解するための補題 -/
theorem unfoldNatLit (x : Nat)
  : (OfNat.ofNat (x + 2) : MyNat) = (OfNat.ofNat (x + 1) : MyNat) + 1 := rfl
macro "expand_num" : tactic => `(tactic| focus
  simp only [unfoldNatLit]
  -- 標準の Nat の輪を簡単な形にする
  simp only [Nat.reduceAdd]
  -- OfNat.ofNat を消す
  dsimp only [OfNat.ofNat] -- dsimp は関数や記法を定義に展開する
  simp only [
    show MyNat.ofNat 1 = 1 from rfl,
    show MyNat.ofNat 0 = 0 from rfl
  ]
)

example (n : MyNat) : 3 * n = 2 * n + 1 * n := by
  expand_num
  guard_target =ₛ (1 + 1 + 1) * n = (1 + 1) * n + 1 * n
  simp only [MyNat.add_mul]

/-- 分配法則を適用して足し算を式の外側に持ってくる -/
macro "distrib" : tactic => `(tactic| focus
  expand_num
  simp only [
    MyNat.mul_add,
    MyNat.add_mul,
    MyNat.mul_zero,
    MyNat.zero_mul,
    MyNat.mul_one,
    MyNat.one_mul
  ]
  ac_rfl
)

example (m n : MyNat) : (m + 4) * n + n = m * n + 5 * n := by
  distrib

-- example (m n : MyNat) : m * n + n * n = (m + n) * n := by
--   distrib -- simp made no progress エラー

macro "expand_num" : tactic => `(tactic| focus
  -- try を付け加えて 進捗がなくてもエラーにしない
  try simp only [unfoldNatLit, Nat.reduceAdd]
  try dsimp only [OfNat.ofNat]
  try simp only [
    show MyNat.ofNat 1 = 1 from rfl,
    show MyNat.ofNat 0 = 0 from rfl
  ]
)

macro "distrib" : tactic => `(tactic| focus
  expand_num
  try simp only [
    MyNat.mul_add,
    MyNat.add_mul,
    MyNat.mul_zero,
    MyNat.zero_mul,
    MyNat.mul_one,
    MyNat.one_mul
  ]
  try ac_rfl
)

example (m n : MyNat) : m * n + n * n = (m + n) * n := by
  distrib -- 成功する

-- 練習問題
example (n : MyNat) : ∃ s t : MyNat, s * t = n * n + 8 * n + 16 := by
  -- (n + 4)^2 なので s=t=n+4 にすれば成功する
  exists (n + 4), (n + 4)
  distrib

example (n : MyNat) : ∃ s t : MyNat, s * t = n * n + 8 * n + 16 := by
  exists 1, n * n + 8 * n + 16
  distrib
