import LeanBook.IntMathlib.Mul

-- 二項関係 (· ≤ ·) が以下のを満たす時 前順序 (preorder) である、と言う
--   反射律 ∀ x ∈ X, x ≤ x
--   推移律 ∀ x,y,z ∈ X, x ≤ y ∧ y ≤ z ⇒ x ≤ z

/-- 定義関数を返す -/
private def MyInt.const (z : MyInt) : MyInt → MyInt := fun _ => z
#check_failure MyInt.const (0 : MyNat) -- Application type mismatch

/-- 自然数から整数への変換 -/
def MyInt.ofMyNat (n : MyNat) : MyInt := ⟦(n, 0)⟧
#check MyInt.const (.ofMyNat 0)

-- 型強制(coercion)で自動的に変換する Coe 型クラスのインスタンスを登録
/-- MyNat から MyInt への型強制 -/
instance : Coe MyNat MyInt where
  coe := MyInt.ofMyNat

#check MyInt.const (0 : MyNat) -- MyNat を渡しても成功する

example : ((0 : MyNat) : MyInt) = (0 : MyInt) := by
  -- 内部実装である MyInt.ofMyNat が見えてしまう。これを見えないようにしたい
  guard_target =ₛ MyInt.ofMyNat 0 = 0
  sorry

-- MyInt.ofMyNat を型キャストとして認識させる
attribute [coe] MyInt.ofMyNat

@[simp]
theorem MyInt.ofMyNat_zero_eq_zero : MyInt.ofMyNat 0 = (0 : MyInt) := by
  dsimp [MyInt.ofMyNat]
  rfl

example : ((0 : MyNat) : MyInt) = (0 : MyInt) := by
  -- 内部実装を意識しなくて済むようになった
  -- このとき InfoView 上には ⊢ ↑0 = 0 と表示される
  -- ↑ uparrow は 型強制（Coercion）を示す記号
  guard_target =ₛ ↑(0 : MyNat) = (0 : MyInt) -- guard_target の =ₛ だと ↑0 = 0 と書けない
  simp

@[norm_cast] -- 型キャストを扱うためのタクティクが利用できるようにする
theorem MyInt.ofMyNat_inj {m n : MyNat}
    : (m : MyInt) = (n : MyInt) ↔ m = n := by
  constructor <;> intro h
  case mp => -- ⊢ m = n
    -- h : ↑m = ↑n (この m n は MyNat 自然数)
    -- 商に送って等しい関係を利用して (m, 0) ≈ (n, 0) にできる
    have : (m, 0) ≈ (n, 0) := Quotient.exact h
    -- ≈ の定義を展開し、MyNat の加法等式へ帰着させる
    notation_simp at this -- Try this: simp only [PreInt.sr, sr_def] at this
    -- 自然数の加法単位元（add_zero）を用いて目標の等式を得る
    simp_all -- Try this: simp_all only [_root_.add_zero, _root_.zero_add]
  case mpr => -- ⊢ ↑m = ↑n
    -- h : m = n
    -- MyNat における等号を型強制の引数に適用
    rw [h]

@[simp]
theorem MyInt.ofMyNat_eq_zero {n : MyNat} : (n : MyInt) = 0 ↔ n = 0 := by
  constructor <;> intro h
  · -- h : ↑n = 0, ⊢ n = 0
    rw [show (0 : MyInt) = ↑ (0 : MyNat) from rfl] at h
    -- h : ↑n = ↑0
    norm_cast at h
  · simp_all

/-- ↑ (m + n) = ↑m + ↑n -/
@[push_cast]
theorem MyInt.ofNat_add (m n : MyNat)
  : ↑ (m + n) = (m : MyInt) + (n : MyInt) := by
  rfl

-- 整数に 自然数を足し算する ことで m ≤ n を構成する
/-- 整数の広義順序 -/
def MyInt.le (m n : MyInt) : Prop :=
  ∃ k : MyNat, m + ↑k = n

instance : LE MyInt where
  le := MyInt.le

@[notation_simp]
theorem MyInt.le_def (m n : MyInt) : m ≤ n ↔ ∃ k : MyNat, m + ↑k = n := by
  rfl

/-- 整数の狭義順序 -/
def MyInt.lt (m n : MyInt) : Prop :=
  m ≤ n ∧ ¬ n ≤ m

instance : LT MyInt where
  lt := MyInt.lt

-- 後で使いたいので記法も登録しておく
@[notation_simp]
theorem MyInt.lt_def (a b : MyInt) : a < b ↔ a ≤ b ∧ ¬ (b ≤ a) := by
  rfl

-- 反射律
@[refl]
theorem MyInt.le_refl (m : MyInt) : m ≤ m := by
  exists 0
  simp

-- 推移律
theorem MyInt.le_trans {m n k : MyInt} (hnm : n ≤ m) (hmk : m ≤ k) : n ≤ k := by
  -- 和の等式で展開
  notation_simp at *
  -- ⊢ ∃ k_1, n + ↑k_1 = k
  -- hnm : ∃ k, n + ↑k = m
  -- hmk : ∃ k_1, m + ↑k_1 = k
  obtain ⟨a, ha⟩ := hnm
  obtain ⟨b, hb⟩ := hmk
  -- ha : n + ↑a = m
  -- hb : m + ↑b = k

  -- このとき a + b が求める条件を満たす
  use a + b -- ⊢ n + ↑(a + b) = k
  push_cast -- ⊢ n + (↑a + ↑b) = k
  have : n + (↑a + ↑b) = k := calc
    _ = (n + ↑a) + ↑b := by ac_rfl
    _ = m + ↑b := by rw [ha]
    _ = k := by rw [hb]
  assumption

-- calc タクティクで使えるように Trans 型クラスのインスタンスにする
instance : Trans (· ≤ · : MyInt → MyInt → Prop) (· ≤ ·) (· ≤ ·) where
  trans := MyInt.le_trans

instance : Preorder MyInt where
  le_refl := MyInt.le_refl
  le_trans := by
    intro _ _ _ hab hbc
    apply MyInt.le_trans hab hbc

-- order : mathlib で提供される 順序関係を扱う専用のタクティク
example (a b c : MyInt) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  order

-- 練習問題
example (a b : MyInt) (h1 : a ≤ b) (h2 : ¬ (a < b)) : b ≤ a := by
  sorry
