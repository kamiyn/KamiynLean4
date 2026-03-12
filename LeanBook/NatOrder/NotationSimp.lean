import LeanBook.NatOrder.StrictOrder
import LeanBook.NatOrder.NotationSimpTag

theorem MyNat.lt_def (m n : MyNat) : m < n ↔ m + 1 ≤ n := by
  rfl

section
  /- ## simp で展開するテスト -/
  -- この section の中でのみ simp に登録する
  attribute [local simp] MyNat.lt_def

  example (m n : MyNat) : m < n := by
    simp -- simp は 登録されているすべての simp ルールを展開する。どれを展開するかがこの行で直観的にわからない
    guard_target =ₛ m + 1 ≤ n
    sorry
  end

section

open Lean Parser Tactic

/-- + や ≤ など 演算子や記法を定義に展開する -/
syntax "notation_simp" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| notation_simp $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp only [notation_simp, $args,*] $[at $location]?)

end

-- < の定義を展開する定理に [notation_simp] 属性を付与する
attribute [notation_simp] MyNat.lt_def

example (m n : MyNat) : m < n := by
  -- notation_simp が使える
  notation_simp
  -- 定義に展開された
  guard_target =ₛ m + 1 ≤ n
  sorry

example (m n : MyNat) (h : m < n) : m + 1 ≤ n := by
  -- rw タクティクやsimpタクティクと同様の at 構文が仕様できる
  notation_simp at *
  -- assumption
  exact h

-- simp の挙動には変化がない
-- example (m n : MyNat) : m < n := by
--   simp -- simp made no progress エラー になる

section

open Lean Parser Tactic

/-- + や ≤ など 演算子や記法を定義に展開する -/
syntax "notation_simp?" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| notation_simp? $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp? only [notation_simp, $args,*] $[at $location]?)
  -- ↑ 違いは simp? になっているだけ
end

example (m n : MyNat) : m < n := by
  notation_simp? -- Try this: simp only [MyNat.lt_def] と表示される
  sorry

-- 練習問題
-- 次の流れで解けず
-- example (a b : MyNat) (h1 : a < b) (h2 : b < a) : False := by
--   notation_simp at *
--   rw [MyNat.le_iff_add] at h1
--   obtain ⟨k1, hk1⟩ := h1 -- hk1 : a + 1 + k1 = b
--   have h3 : a + 1 + k1 + 1 ≤ a := by
--     rw [hk1] -- b + 1 + k2 = a
--     exact h2
--   -- ここから下で a をキャンセルする書き方がわからなかった
--   have : k1 + 1 + 1 ≤ 0 := by
--     rw[show a + 1 + k1 + 1 = a + (k1 + 1 + 1) from by ac_rfl] at h3
--     simp_all

example (a b : MyNat) (h1 : a < b) (h2 : b < a) : False := by
  notation_simp at *
  have : b + 1 ≤ b := calc
    _ ≤ a := by apply h2
    _ ≤ a + 1 := by exact MyNat.le_add_one_right a
    _ ≤ b := by apply h1

  rw [MyNat.le_iff_add] at this -- this : ∃ k, b + 1 + k = b 和の等式に置き換える
  obtain ⟨k, hk⟩ := this
  -- b + 1 + k = b の両辺の b をキャンセルする
  have : 1 + k = 0 := by
    rw [show b + 1 + k = b + (1 + k) from by ac_rfl] at hk
    simp_all
  simp_all -- 1 + k = 0 なので ⊢ False が満たされた

-- 等式の状態で展開した後 n + 1 = 0 の形に持ち込む。等式だけの方が理解しやすい
-- その時点で得られている仮定に対し 交換・結合法則を適用し、簡約可能な状態にするのは
-- rw [show X = Y from by ac_rfl] at H のパターン で頻出
example (a b : MyNat) (h1 : a < b) (h2 : b < a) : False := by
  notation_simp at * -- ≤ の形にすることで 和の等式に置き換え可能にする
  rw [MyNat.le_iff_add] at * -- 和の等式に置き換える
  obtain ⟨k1, hk1⟩ := h1 -- hk1 : a + 1 + k1 = b
  obtain ⟨k2, hk2⟩ := h2 -- hk2 : b + 1 + k2 = a
  have h3 : a + 1 + k1 + 1 + k2 = a := by
    rw [hk1]
    exact hk2
  have : k1 + k2 + 1 + 1 = 0 := by
    -- a + n = a の形になるよう 結合法則 を利用
    rw [show a + 1 + k1 + 1 + k2 = a + (1 + k1 + 1 + k2) from by ac_rfl] at h3
    simp_all
  simp_all
