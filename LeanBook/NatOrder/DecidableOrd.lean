import LeanBook.NatOrder.PartialOrder

example : 0 ≤ 1 := by
  apply MyNat.le_step -- 0 ≤ 0 に変換
  apply MyNat.le.refl

example : 0 ≤ 3 := by
  apply MyNat.le_step -- 0 ≤ 2 に変換 (1.succ として見える)
  apply MyNat.le_step -- 0 ≤ 1 に変換 (0.succ として見える)
  apply MyNat.le_step -- 0 ≤ 0 に変換
  apply MyNat.le.refl

-- Decidable 型により 命題が 決定可能 であることを表す
-- 決定可能 ≒ Pが成り立つかどうか計算するアルゴリズムが存在する
-- 標準ライブラリの定義
-- class inductive Decidable (p : Prop) where
--   /-- ¬ p の証明があるなら p は決定可能 -/
--   | isFalse (h : ¬ p) : Decidable p
--   /-- p の証明があるなら p は決定可能 -/
--   | isTrue (h : p) : Decidable p

-- a = b を Decidable のインスタンスにしたいケースはよくあり
-- 省略形 DecidableEq という型クラスが用意されている

-- deriving を使うことで DecidableEq 型クラス のインスタンスになる
deriving instance DecidableEq for MyNat
-- その結果 decide タクティクで証明できるようになる

example : 32 + 13 ≠ 46 := by
  decide

#eval 1 ≠ 2

def MyNat.ble (a b : MyNat) : Bool :=
  match a, b with
  -- a = 0 の場合は 常に a ≤ b が成り立つ
  | 0, _ => true
  -- a ≠ 0 かつ b = 0 の場合は、常に ¬ a ≤ b が成り立つ
  | _ + 1, 0 => false -- 意味的には a + 1, 0 => false なのだが unused variable `a` と警告が出るので アンダースコアを使う
  -- それ以外の場合 を再帰的に計算
  | a + 1, b + 1 => MyNat.ble a b
-- すべてのケースが記述できた

#eval MyNat.ble 0 1
#eval MyNat.ble 1 0
#eval MyNat.ble 3 12

instance (a b : MyNat) : Decidable (a ≤ b) := by
  apply decidable_of_iff (MyNat.ble a b = true)
  guard_target =ₛ a.ble b = true ↔ a ≤ b
  sorry

-- functional induction により 2つの引数についての関数の帰納法
#check MyNat.ble.induct
-- MyNat.ble.induct (motive : MyNat → MyNat → Prop) (case1 : ∀ (b : MyNat), motive MyNat.zero b)
--   (case2 : ∀ (n : MyNat), motive n.succ MyNat.zero) (case3 : ∀ (a b : MyNat), motive a b → motive a.succ b.succ)
--   (a b : MyNat) : motive a b

@[simp] theorem MyNat.ble_zero_left (n : MyNat) : MyNat.ble 0 n = true := by
  rfl

@[simp] theorem MyNat.ble_zero_right (n : MyNat) : MyNat.ble (n + 1) 0 = false := by
  rfl

@[simp] theorem MyNat.ble_succ (m n : MyNat)
  : MyNat.ble (m + 1) (n + 1) = MyNat.ble m n := by rfl

-- 以下の定義で case1 から induction m, n より前の4行は #check MyNat.ble.induct で得られる型と同じ
def MyNat.ble.inductAux (motive : MyNat → MyNat → Prop)
    (case1 : ∀ (n : MyNat), motive 0 n)
    (case2 : ∀ (n : MyNat), motive (n + 1) 0)
    (case3 : ∀ (m n : MyNat), motive m n → motive (m + 1) (n + 1))
    (m n : MyNat) : motive m n := by
  induction m, n using MyNat.ble.induct with
  | case1 n => apply case1
  | case2 n => apply case2
  | case3 m n h => apply case3; assumption

-- theorem MyNat.le_impl は上から書くのではなく
-- 次のように induction の分岐構造を先に書いてから 間を埋めると InfoView で状況が見える
-- theorem MyNat.le_impl (m n : MyNat) : MyNat.ble m n = true ↔ m ≤ n := by
--   induction m, n using MyNat.ble.inductAux with
--   | case1 n =>
--     sorry
--   | case2 n =>
--     sorry
--   | case3 m n ih =>
--     sorry

-- 本にあった dsimp [MyNat.ble] は効果が無いようだったためコメントアウト
-- simp と違って dsimp は効果がなくても警告にならない
theorem MyNat.le_impl (m n : MyNat) : MyNat.ble m n = true ↔ m ≤ n := by
  induction m, n using MyNat.ble.inductAux with
  | case1 n => -- m = 0 のケース ⊢ ble 0 n = true ↔ 0 ≤ n
    simp -- Try this: simp_all only [MyNat.ble_zero_left, MyNat.zero_le]
  | case2 n => -- n = 0 のケース ⊢ (n + 1).ble 0 = true ↔ n + 1 ≤ 0
    -- dsimp [MyNat.ble]
    suffices ¬ n + 1 ≤ 0 from by simp_all
    -- Try this: simp_all only [le_zero, add_eq_zero_iff_eq_zero, one_neq_zero,
    --   and_false, not_false_eq_true, ble_zero_right, Bool.false_eq_true]
    intro h -- h : n + 1 ≤ 0
    contradiction -- h が矛盾
  | case3 m n ih =>
    -- ih : m.ble n = true ↔ m ≤ n
    -- ⊢ (m + 1).ble (n + 1) = true ↔ m + 1 ≤ n + 1
    -- 帰納法に持ち込む
    -- dsimp [MyNat.ble]
    simp [ih]

-- suffices ¬ n + 1 ≤ 0 from by simp_all を使わない
example (m n : MyNat) : MyNat.ble m n = true ↔ m ≤ n := by
  induction m, n using MyNat.ble.inductAux with
  | case1 n => -- m = 0 のケース ⊢ ble 0 n = true ↔ 0 ≤ n
    -- 前方・後方どちらの含意も true
    simp
  | case2 n => -- n = 0 のケース ⊢ (n + 1).ble 0 = true ↔ n + 1 ≤ 0
    -- 前方・後方どちらの含意も同じ流れで矛盾を導く <;> を使うと1行で書ける
    constructor <;> intro h <;> contradiction
    -- constructor
    -- · -- ⊢ (n + 1).ble 0 = true → n + 1 ≤ 0
    --   intro h
    --   contradiction
    -- · -- ⊢ n + 1 ≤ 0 → (n + 1).ble 0 = true
    --   intro h
    --   contradiction
  | case3 m n ih =>
    -- 1. ble (m+1) (n+1) は定義により ble m n に簡約される
    -- 2. m+1 ≤ n+1 は succ_le_succ 性質により m ≤ n と同値になる
    -- これらにより、帰納法の仮定 ih とゴールが一致する
   simp [ih]

/-- 広義の順序関係 (· ≤ ·) を 決定可能にする -/
instance : DecidableLE MyNat := fun n m =>
  decidable_of_iff (MyNat.ble n m = true) (MyNat.le_impl n m)

#eval 1 ≤ 3
#eval 12 ≤ 13
example : 1 ≤ 9 := by decide
example : 32 ≤ 47 := by decide

theorem MyNat.lt_impl (m n : MyNat) : MyNat.ble (m + 1) n ↔ m < n := by
  rw [MyNat.le_impl] -- ⊢ m + 1 ≤ n ↔ m < n
  rfl -- 狭義の順序関係の定義

instance : DecidableLT MyNat := fun n m =>
  decidable_of_iff (MyNat.ble (n + 1) m = true) (MyNat.lt_impl n m)

example : 1 < 4 := by decide

-- 練習問題
-- 解答がないのは 生成プログラム上の不具合らしい https://github.com/LambdaNote/errata-leanbook-1-1/issues/129
example : 23 < 32 ∧ 12 ≤ 24 := by
  constructor
  · decide
  · decide

-- <;> を利用して1行化。上記 suffices ¬ n + 1 ≤ 0 from by simp_all を使わない でも使った
example : 23 < 32 ∧ 12 ≤ 24 := by
  constructor <;> decide
