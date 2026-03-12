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
