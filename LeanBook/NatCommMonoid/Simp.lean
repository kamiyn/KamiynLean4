import LeanBook.NatCommMonoid.Induction

example (n : MyNat) : 0 + (n + 0) = n := by
  -- 最初は simp で証明できない。attribute [simp] の行を前に記述すると失敗する
  fail_if_success simp
  -- 明示的に rw で証明する
  rw [MyNat.add_zero, MyNat.zero_add]

attribute [simp] MyNat.add_zero MyNat.zero_add

example (n : MyNat) : 0 + (n + 0) = n := by
  -- simp で証明できるようになった
  simp

-- simp に手動で命題を渡すこともできる
theorem MyNat.ctor_eq_zero : MyNat.zero = 0 := by rfl
example : MyNat.zero = 0 := by
  simp [MyNat.ctor_eq_zero]

attribute [simp] MyNat.add_succ

-- ローカルコンテキストにおける仮定を単純化させる
example (m n : MyNat) (h : m + n + 0 = n + m) : m + n = n + m := by
  simp at h -- simp? の表示は Try this: simp only [MyNat.add_zero] at h
  guard_hyp h : m + n = n + m
  exact h -- 本では rw[h] と書かれているが この時点で書き換えなしに一致している

-- ローカルコンテキストのすべての仮定とゴールを単純化する
example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  simp at *
  guard_hyp h : m = n
  guard_target =ₛ m = n -- =ₛ は 構文的同値 (Syntactic) 例えば通常の自然数において n + 0 と n に対して =ₛ は一致しない。一方単純な = だと一致する
  exact h -- 本では rw[h] と書かれているが この時点で書き換えなしに一致している

-- これ以上単純化できないところまで単純化する。一発で終了する
example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  simp_all

-- @[simp] タグにより定義と同時に attribute [simp] のようにグローバル簡約集合（Simp set）への登録をする
@[simp] theorem MyNat.succ_add (m n : MyNat) : MyNat.succ m + n = MyNat.succ (m + n) := by
  induction n
  case zero => rfl
  case succ n' ih =>
    simp [ih]
    -- ih だけではなく attribute [simp] MyNat.add_succ で登録された add_succ も適用される

example (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n
  case zero => rfl
  case succ n' ih =>
    simp? [ih] -- Try this: simp only [MyNat.add_succ, ih]

-- calc で途中経過を明示する
example (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n
  case zero => rfl
  case succ n' ih => calc
  -- 左辺を _ で省略すると ゴールの左辺だと認識される
    _ = (m.succ + n').succ := by rw [MyNat.add_succ]
    -- https://github.com/LambdaNote/errata-leanbook-1-1/issues/74
    -- MyNat.succ_add が中で帰納法を適用しておりここでは ih の利用が良いと思われる
    -- calc の利用方法を学習する観点では関係がない
    _ = (m + n').succ.succ := by rw [ih] -- MyNat.succ_add
    _ = (m + n'.succ).succ := by rw [← MyNat.add_succ] -- rw は双方向に書き換えるので本にあるように ← なしでもよい

example (n : MyNat) : 1 + n = n + 1 := calc
  _ = .succ 0 + n := by rfl -- 1 + n を定義に沿って展開
  _ = .succ (0 + n) := by rw [MyNat.succ_add]
  _ = .succ n := by rw[MyNat.zero_add]
  -- 次の行なしでも成功する
  _ = n + 1 := by rfl

-- 練習問題
example (n : MyNat) : 2 + n = n + 2 := calc
  _ = .succ 1 + n := by rfl -- 1 + n を定義に沿って展開
  _ = .succ (1 + n) := by rw [MyNat.succ_add]
  _ = .succ (.succ 0 + n) := rfl
  _ = .succ (.succ (0 + n)) := by rw [MyNat.succ_add]
  _ = .succ (.succ n) := by rw [MyNat.zero_add]

-- 上は calc による進行を再帰的に展開したものだった
example (n : MyNat) : 2 + n = n + 2 := by
  induction n
  case zero => rfl
  case succ n' ih => simp [ih]
