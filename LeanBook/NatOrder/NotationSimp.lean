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
example (a b : MyNat) (h1 : a < b) (h2 : b < a) : False := by
  sorry
