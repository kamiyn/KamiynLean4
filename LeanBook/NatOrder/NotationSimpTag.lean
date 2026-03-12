import Lean

/-- + や ≤ など 演算子や記号を定義に展開するためのルールを登録する (同一ファイル内では効果を発揮しない) -/
register_simp_attr notation_simp
