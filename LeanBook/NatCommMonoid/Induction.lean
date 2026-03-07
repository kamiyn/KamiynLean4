import LeanBook.NatCommMonoid.TypeClass

-- example (n: MyNat) : 0 + n = n := by
--   rfl
-- tactic 'rfl' failed, the left-hand side
--   0 + n
-- is not definitionally equal to the right-hand side
--   n

#reduce fun (n : MyNat) => n + 0
#reduce fun (n : MyNat) => 0 + n

set_option pp.fieldNotation.generalized false in

example (n : MyNat) : 0 + n = n := by
  -- n についての帰納法で証明する
  induction n with
  -- MyNat のコンストラクタが zero と succ (n : MyNat) なので、それらでパターン分けする
  | zero =>
    -- ゴールが ⊢ 0 + MyNat.zero = MyNat.zero という形になる
    guard_target =ₛ 0 + MyNat.zero = MyNat.zero
    -- 変数がないのでrflで証明できる
    rfl
  -- n = succ n' のケース
  | succ n' ih =>
    -- ゴールが ⊢ 0 + MyNat.succ n' = MyNat.succ n'
    guard_target =ₛ 0 + MyNat.succ n' = MyNat.succ n'
    -- 帰納法の仮定 ih が手に入る
    guard_hyp ih : 0 + n' = n'
    sorry

-- induction n with と | の記法他に induction n と case の書き方もある
-- case の書き方の方が C# に近い
