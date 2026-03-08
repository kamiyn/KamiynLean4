import LeanBook.NatCommMonoid.AcRfl

example (m n : MyNat) : m + n = n + m := by
  induction n
  case zero =>
    -- m + 0 = 0 + m になって欲しい
    guard_target =ₛ m + MyNat.zero = MyNat.zero + m
    simp [MyNat.ctor_eq_zero]
  case succ n ih =>
    -- m + (n + 1) = (n + 1) + m になって欲しい
    guard_target =ₛ m + MyNat.succ n = MyNat.succ n + m
    simp [ih]

#check MyNat.rec

-- 帰納法で記法が崩れるのを防ぐ
/-- MyNat 用の帰納法の原理を書き直したもの -/
def MyNat.recAux.{u} {motive : MyNat → Sort u}
  (zero : motive 0)
  (succ : (n : MyNat) → motive n → motive (n + 1)) (t : MyNat) : motive t :=
  match t with
  | .zero => zero
  | .succ n => succ n (MyNat.recAux zero succ n)

attribute [induction_eliminator] MyNat.recAux

example (m n : MyNat) : m + n = n + m := by
  induction n
  case zero =>
    guard_target =ₛ m + 0 = 0 + m
    simp -- simp [MyNat.ctor_eq_zero] は使えなくなっている
  case succ n ih =>
    guard_target =ₛ m + (n + 1) = (n + 1) + m
    ac_rfl

-- 練習問題
/-- 1つ前 の自然数を返す関数。ゼロに対してはゼロを返す -/
private def MyNat.pred (n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => n

private theorem MyNat.pred0: MyNat.pred 0 = 0 := by rfl
private theorem MyNat.pred1: MyNat.pred 1 = 0 := by rfl

example (n : MyNat) : MyNat.pred (MyNat.pred n + 1) = MyNat.pred n := by
  induction n
  case zero =>
    simp[MyNat.pred0]
    simp[MyNat.pred1]
  case succ n' ih =>
    -- n' : MyNat
    -- ih : MyNat.pred (MyNat.pred n' + 1) = MyNat.pred n'
    -- ⊢ MyNat.pred (MyNat.pred (n' + 1) + 1) = MyNat.pred (n' + 1)
    --
    -- 左辺 MyNat.pred (MyNat.pred (n' + 1) + 1)
    -- 内側の MyNat.pred (n' + 1) が 関数定義の n + 1 => n にマッチするため n' になる
    -- 左辺はその結果として MyNat.pred (n' + 1)
    -- この時点で 右辺と一致するので rfl でいける
    rfl

-- 本の解答 最後の rfl を theorem にして rw で適用
private theorem MyNat.pred_add_one (n : MyNat): MyNat.pred (n + 1) = n := by rfl
example (n : MyNat) : MyNat.pred (MyNat.pred n + 1) = MyNat.pred n := by
  rw[MyNat.pred_add_one]

-- Genimi: ケース分割を使う
example (n : MyNat) : MyNat.pred (MyNat.pred n + 1) = MyNat.pred n := by
  cases n
  case zero => rfl -- 0 のケースも計算で解ける
  case succ n' => rfl -- succ のケースも計算で解ける

-- https://github.com/LambdaNote/errata-leanbook-1-1/issues/80
-- 実は rfl だけで解ける
example (n : MyNat) : MyNat.pred (MyNat.pred n + 1) = MyNat.pred n := by
  rfl

-- 差し替え予定の練習問題
/-- 再帰的に定義された、入力された自然数を2倍にする関数 -/
private def MyNat.double (n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => (MyNat.double n) + 2

example (n : MyNat) : n.double.double = n + n + n + n := by
  induction n
  case zero => rfl
  case succ n ih => calc
    -- ⊢ MyNat.double (MyNat.double (n + 1))
    --   = n + 1 + (n + 1) + (n + 1) + (n + 1)
    -- 以下の rfl の連鎖は 最後の1回だけあれば そこまでは自動的に簡約してくれる
    _ = MyNat.double (MyNat.double (n + 1)) := by rfl
    _ = MyNat.double (MyNat.double (n) + 2) := by rfl
    _ = MyNat.double (MyNat.double (n) + 1 + 1) := by rfl
    _ = MyNat.double (MyNat.double (n) + 1) + 2 := by rfl
    _ = MyNat.double (MyNat.double (n)) + 2 + 2 := by rfl
    _ = n + n + n + n + 2 + 2 := by rw[ih]
    _ = (n + 1) + (n + 1) + (n + 1) + (n + 1) := by ac_rfl

-- 以下はうまくいかず。組み込みの Nat を使う環境であればいけるのかもしれない
-- これがうまくいかないからこそ rfl 一発で済まないような練習問題にしたとも想像されうる
-- example (n : MyNat) : n.double.double = n + n + n + n := by
--   induction n
--   case zero => rfl
--   case succ n ih =>
--     dsimp [MyNat.double]
--     rw [ih]
--     ac_rfl

-- Gemini の支援を得て calc の流れを calc なしにするように変形
-- InfoView 見ながら作業する分にはこちらの方がやりやすい
example (n : MyNat) : n.double.double = n + n + n + n := by
  induction n
  case zero => rfl
  case succ n ih =>
    -- change により ⊢ を変更する。calc では by rfl に相当
    change MyNat.double (MyNat.double n) + 2 + 2 = _
    rw [ih]
    ac_rfl
