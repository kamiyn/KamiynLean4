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

example (n : MyNat) : MyNat.pred (MyNat.pred n + 1) = MyNat.pred n := by
  sorry
