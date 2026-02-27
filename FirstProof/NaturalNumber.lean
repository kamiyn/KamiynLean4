-- ペアノの公理
-- 機能型を定義する
inductive MyNat where
  | zero -- コンストラクタ
  | succ (n : MyNat) -- コンストラクタ

#check MyNat.zero
#check MyNat.succ

#check MyNat.succ .zero

def MyNat.one := MyNat.succ .zero
def MyNat.two := MyNat.succ .one

-- #eval MyNat.two

def MyNat.add (m n : MyNat) : MyNat :=
  match n with -- パターンマッチの対象 n
  | .zero => m -- 名前空間 MyNat を省略
  | .succ n => succ (add m n) -- ここの n は パターンマッチの対象 n とスコープが異なる

#check MyNat.add .one .one

set_option pp.fieldNotation.generalized false -- フィールド記法

#reduce MyNat.add .one .one
#reduce MyNat.two

/-- 1 + 1 = 2 の MyNat における証明 --/
example : MyNat.add .one .one = .two := by
  rfl -- ゴールを表示するには rfl の **先頭** にカーソルを置く
-- example : 命題に名前を付けずに証明する
-- rfl : タクティク と呼ばれるものの1つ
