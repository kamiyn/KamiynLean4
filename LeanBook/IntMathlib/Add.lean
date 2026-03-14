import LeanBook.Int.Basic
import Mathlib.Tactic

-- MyInt に足し算を定義
-- Quotient.lift は 1引数関数向け
-- 足し算(2引数) の場合 Quotient.lift₂ を使う

def PreInt.add (m n : PreInt) : MyInt :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => ⟦(m₁ + n₁, m₂ + n₂)⟧

/-- 整数 MyInt の足し算 -/
def MyInt.add : MyInt → MyInt → MyInt := Quotient.lift₂ PreInt.add <| by
  intro (m₁, m₂) (n₁, n₂) (m'₁, m'₂) (n'₁, n'₂) rm rn
  dsimp [PreInt.add] -- ⊢ ⟦(m₁ + n₁, m₂ + n₂)⟧ = ⟦(m'₁ + n'₁, m'₂ + n'₂)⟧
  apply Quotient.sound
  --「商に送って等しい」 自然な写像 α → α/sr による像が等しい
  -- Quotient.sound により、商集合上の等式を台集合上の同値関係 ≈ へ還元する
  -- ⊢ (m₁ + n₁, m₂ + n₂) ≈ (m'₁ + n'₁, m'₂ + n'₂)
  notation_simp -- Try this: simp only [MyInt.sr_def]

  -- ⊢ m₁ + n₁ + (m'₂ + n'₂) = m₂ + n₂ + (m'₁ + n'₁)
  -- rm : (m₁, m₂) ≈ (m'₁, m'₂)
  -- rn : (n₁, n₂) ≈ (n'₁, n'₂)
  have : m₁ + n₁ + (m'₂ + n'₂) = m₂ + n₂ + (m'₁ + n'₁) := calc
    _ = (m₁ + m'₂) + (n₁ + n'₂) := by ac_rfl
    _ = (m₂ + m'₁) + (n₂ + n'₁) := by rw [rm, rn]
    _ = m₂ + n₂ + (m'₁ + n'₁) := by ac_rfl

  assumption

instance instAddMyInt : Add MyInt where
  add := MyInt.add

-- 足し算が使えるようになった
#check (3 + 4 : MyInt)

@[simp]
theorem MyInt.add_def (x₁ x₂ y₁ y₂ : MyNat)
    : ⟦(x₁, y₁)⟧ + ⟦(x₂, y₂)⟧ = (⟦(x₁ + x₂, y₁ + y₂)⟧ : MyInt) := by
  dsimp [(· + ·), Add.add, MyInt.add, PreInt.add]

-- notation_simp で簡単に展開できるようにする
attribute [notation_simp] PreInt.sr PreInt.r

/-- notation_simp に使用させるための補題 -/
@[notation_simp, simp] theorem MyNat.ofNat_zero : MyNat.ofNat 0 = 0 := rfl

theorem MyInt.add_zero (m : MyInt) : m + 0 = m := by
  -- m : MyInt の代表元 a : PreInt を考えると
  -- ∀ (a : PreInt), ⟦a⟧ + 0 = ⟦a⟧ を示せばよい
  refine Quotient.inductionOn m ?_
  -- a : PreInt が与えられたとし、 a = (a₁, a₂) と表されたとする
  intro (a₁, a₂)
  -- このとき同値関係の定義から a₁ + 0 + a₂ = a₂ + 0 + a₁ を示せばよい
  apply Quotient.sound
  notation_simp -- Try this: simp only [PreInt.sr, MyNat.ofNat_zero, PreInt.r]
  ac_rfl

@[simp]
theorem MyInt.zero_add (m : MyInt) : 0 + m = m := by
  refine Quotient.inductionOn m ?_
  -- ⊢ ∀ (a : PreInt), 0 + ⟦a⟧ = ⟦a⟧
  intro (a₁, a₂)
  apply Quotient.sound
  notation_simp
  -- ⊢ 0 + a₁ + a₂ = 0 + a₂ + a₁
  ac_rfl

-- ここで使われている refine タクティクは exact に似ているが
-- メタ変数 ?_ が新しいゴールになる

-- 上記 add_zero, zero_add は中身が同一の証明なのでマクロで書けるか ?
section
  local macro "unfold_int₁" : tactic => `(tactic| focus
    refine Quotient.inductionOn m ?_
    intro (a₁, a₂)
    apply Quotient.sound
    notation_simp
    -- ac_rfl
  )

  example (m : MyInt) : m + 0 = m := by
    fail_if_success unfold_int₁; -- このマクロ適用による証明は失敗する
    sorry
end

section
  -- マクロ衛生を無効にする
  set_option hygiene false

  local macro "unfold_int₁" : tactic => `(tactic| focus
    refine Quotient.inductionOn m ?_
    intro (a₁, a₂)
    apply Quotient.sound
    notation_simp
    -- ac_rfl
  )
  -- macro に ac_rfl を含めない理由 (Gemini の回答)
  -- マクロ unfold_int₁ が行っているのは、商集合という抽象的な皮を剥ぎ、台集合上の関係へと「翻訳」する**「論理的展開（Setup）」です。
  -- 一方で ac_rfl は、展開された等式が結合法則や交換法則によって成立するかを確認する「代数的決定（Solving）」**です。
  -- これは次の "整数に関する命題を自然数の話に帰着させる" という説明で明らかになる

  example (m : MyInt) : m + 0 = m := by
    unfold_int₁ -- マクロ衛生を無効にすると証明が通る
    ac_rfl
end

/-- 整数に関する命題を自然数の話に帰着させる (1変数用) -/
macro "unfold_int₁" : tactic => `(tactic| focus
  intro m -- intro で m を導入する (呼び出し側に revert m を記述する)
  refine Quotient.inductionOn m ?_
  intro (a₁, a₂)
  apply Quotient.sound
  notation_simp
)

example (m : MyInt) : m + 0 = m := by
  revert m -- revert で ゴールを ⊢ ∀ (m : MyInt), m + 0 = m にする
  unfold_int₁
  ac_rfl

example (m : MyInt) : 0 + m = m := by
  revert m -- ⊢ ∀ (m : MyInt), 0 + m = m
  unfold_int₁
  ac_rfl

/-- 整数に関する命題を自然数の話に帰着させる (2変数用) -/
macro "unfold_int₂" : tactic => `(tactic| focus
  intro m n
  refine Quotient.inductionOn₂ m n ?_
  intro (a₁, a₂) (b₁, b₂)
  apply Quotient.sound
  notation_simp
)

/-- 整数に関する命題を自然数の話に帰着させる (3変数用) -/
macro "unfold_int₃" : tactic => `(tactic| focus
  intro m n k
  refine Quotient.inductionOn₃ m n k ?_
  intro (a₁, a₂) (b₁, b₂) (c₁, c₂)
  apply Quotient.sound
  notation_simp
)

theorem MyInt.add_assoc (m n k : MyInt) : m + n + k = m + (n + k) := by
  revert m n k
  unfold_int₃
  ac_rfl

theorem MyInt.add_comm (m n : MyInt) : m + n = n + m := by
  revert m n
  unfold_int₂
  ac_rfl

instance : Std.Associative (α := MyInt) (· + ·) where
  assoc := MyInt.add_assoc

instance : Std.Commutative (α := MyInt) (· + ·) where
  comm := MyInt.add_comm

/-- 整数の引き算 -/
def MyInt.sub (m n : MyInt) : MyInt := m + -n

/-- 引き算を a - b と書けるように型クラスに登録する -/
instance : Sub MyInt where
  sub := MyInt.sub

-- 後で使うので補題として登録しておく
@[simp, notation_simp]
theorem MyInt.sub_def (x y : MyInt) : x - y = x + -y := rfl

theorem MyInt.neg_add_cancel (m : MyInt) : -m + m = 0 := by
  revert m
  unfold_int₁
  ac_rfl

-- アーベル群 (可換群 commutative group) を表す AddCommGroup という型クラスのインスタンスにする
-- アーベル群であるとは
--  単位元 と 結合法則がある (モノイド である)
--  逆元がある (群 である)
--  交換法則を満たす (可換 である)

-- AddCommGroup は abel タクティクで再利用可能にするために
-- Mathlib により提供される型クラス
instance : AddCommGroup MyInt where
  add_assoc := MyInt.add_assoc
  add_comm := MyInt.add_comm
  zero_add := MyInt.zero_add
  add_zero := MyInt.add_zero
  neg_add_cancel := MyInt.neg_add_cancel
  nsmul := nsmulRec -- Mathlib に用意されている nsmulRec
  zsmul := zsmulRec -- Mathlib に用意されている zsmulRec

-- AddCommGroup のインスタンスでは abel というタクティクが使える
example (a b : MyInt) : (a + b) - b = a := by
  abel

-- 練習問題
example (a b c : MyInt) : (a - b) - c + b + c = a := by
  abel
