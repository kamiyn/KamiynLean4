import LeanBook.FirstProof.NaturalNumber

/-- Nat の項から対応するMyNatの項を得る ただし `Nat` はLean組み込みの自然数の型 -/
def MyNat.ofNat (n : Nat) : MyNat :=
  match n with
    | 0 => MyNat.zero
    | n + 1 => MyNat.succ (MyNat.ofNat n)

/-- OfNat のインスタンスを実装する -/
@[default_instance] -- 数値リテラルがLeanの組み込みのNat型の項として解釈されるのを防ぐ
instance (n : Nat) : OfNat MyNat n where
  ofNat := MyNat.ofNat n

-- 数値リテラルが MyNat 型の項　として解釈されるようになった
#check 0
#check 1

-- #check 1 + 1 -- この時点では + が登録されていないので失敗する

/-- MyNat.add を 足し算として登録する -/
instance : Add MyNat where
  add := MyNat.add

-- + 演算が MyNat として使えるようになった
#check 1 + 1
#check MyNat.zero + MyNat.zero
#eval 0 + 0
#eval 1 + 2
-- 1 + 2 の結果は MyNat.succ の連鎖になった

-- Repr という型クラスのインスタンスを実装
def MyNat.toNat (n : MyNat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => MyNat.toNat n + 1

-- 「ユーザーに表示可能な（文字列のような）形式」に変換
-- ここでは 組み込みの Nat 型に変換することで実現している
instance : Repr MyNat where
  reprPrec n _ := repr n.toNat -- _アンダースコアは演算子の優先順位 引数

#eval 0 + 0
#eval 1 + 1

example (n: MyNat) : n + 0 = n := by
  rfl
