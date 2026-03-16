variable {α : Type} {a₁ a₂ : α}

example (f : α → α) (h : a₁ = a₂) : f (f a₁) = f (f a₂) := by
  grind

set_option trace.grind.assert true in
set_option trace.grind.eqc true in

theorem easy_proof (P : Prop) (h : P) : P := by
  grind
  -- [grind.assert] P
  -- [grind.eqc] P = True
  -- [grind.assert] ¬P
  -- [grind.eqc] P = False

#print axioms easy_proof
-- 'easy_proof' depends on axioms: [propext, Classical.choice, Quot.sound]

set_option trace.grind.assert false in
set_option trace.grind.eqc false in

-- grind のカスタマイズ
-- grind = について
def f : Nat → Nat := fun x => x - 1
def g : Nat → Nat := fun x => x + 1
@[grind =]
theorem fg (x : Nat) : f (g x) = x := by
  dsimp [f, g]

example (a b c : Nat) (h1 : f a = b) ( h2 : a = g c) : b =c := by
  grind

-- grind attribute の派生形として @[grind _=_] という属性もある。
-- この @[grind _=_] は左辺・右辺ともにパターンとして登録される

-- 命題のパターンを登録する @[grind →]

/-- 自然数上の広義の順序関係を再定義する -/
inductive Nat.myle (n : Nat) : Nat → Prop
  | refl : Nat.myle n n
  | step {m : Nat} : Nat.myle n m → Nat.myle n (m + 1)

/-- myle を表す記号 標準の ≤ と被らないようにしている -/
-- ここの記述は 演算子と? の間にスペースを空けない など スペースの扱いが重要
infix:50 " ≤? " => Nat.myle
attribute [grind →] Nat.myle.step

variable {m n a b k : Nat}
/-- 推移律 -/
theorem Nat.myle_trans (hnm : n ≤? m) (hmk : m ≤? k) : n ≤? k := by
  induction hmk with grind


-- 左から右にパターンを探す @[grind =>]
/-- 群 の定義 -/
class Group (G : Type) [One G] [Mul G] [Inv G] where
  mul_one : ∀ g : G, g * 1 = g
  one_mul : ∀ g : G, 1 * g = g
  mul_inv : ∀ g : G, g * g⁻¹ = 1
  inv_mul : ∀ g : G, g⁻¹ * g = 1
  mul_assoc : ∀ g₁ g₂ g₃ : G, g₁ * (g₂ * g₃) = (g₁ * g₂) * g₃

variable {G : Type} [One G] [Mul G] [Inv G] [Group G]

attribute [grind =>]
  Group.mul_one Group.one_mul
  Group.mul_inv Group.inv_mul Group.mul_assoc

theorem mul_right_inv {g h : G} (hy : g * h = 1) : h = g⁻¹ := calc
  _ = 1 * h := by grind
  _ = g⁻¹ := by grind

@[grind =>]
theorem mul_left_inv {g h : G} (hy : h * g = 1) : h = g⁻¹ := calc
  _ = h * 1 := by grind
  _ = g⁻¹ := by grind

theorem inv_inv (g : G) : g⁻¹⁻¹ = g := by
  grind
