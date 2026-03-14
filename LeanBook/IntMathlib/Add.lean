import LeanBook.Int.Basic
import Mathlib.Tactic

-- MyInt に足し算を定義
-- Quotient.lift は 1引数関数向け
-- 足し算(2引数) の場合 Quotient.lift₂ を使う

def PreInt.add (m n : PreInt) : MyInt :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => ⟦(m₁ + n₁, m₂ + n₂)⟧

/-- 整数 MyInt の足し算 -/
def MyInt.add : MyInt → MyInt → MyInt := Quotient.lift₂ PreInt.add <| by
  intro (m₁, m₂) (n₁, n₂) (m'₁, m'₂) (n'₁, n'₂) rm rn
  dsimp [PreInt.add] -- ⊢ ⟦(m₁ + n₁, m₂ + n₂)⟧ = ⟦(m'₁ + n'₁, m'₂ + n'₂)⟧
  apply Quotient.sound
  --「商に送って等しい」 自然な写像 α → α/sr による像が等しい
  -- Quotient.sound により、商集合上の等式を台集合上の同値関係 ≈ へ還元する
  -- ⊢ (m₁ + n₁, m₂ + n₂) ≈ (m'₁ + n'₁, m'₂ + n'₂)
  notation_simp -- Try this: simp only [MyInt.sr_def]

  -- ⊢ m₁ + n₁ + (m'₂ + n'₂) = m₂ + n₂ + (m'₁ + n'₁)
  -- rm : (m₁, m₂) ≈ (m'₁, m'₂)
  -- rn : (n₁, n₂) ≈ (n'₁, n'₂)
  have : m₁ + n₁ + (m'₂ + n'₂) = m₂ + n₂ + (m'₁ + n'₁) := calc
    _ = (m₁ + m'₂) + (n₁ + n'₂) := by ac_rfl
    _ = (m₂ + m'₁) + (n₂ + n'₁) := by rw [rm, rn]
    _ = m₂ + n₂ + (m'₁ + n'₁) := by ac_rfl

  assumption

instance instAddMyInt : Add MyInt where
  add := MyInt.add

-- 足し算が使えるようになった
#check (3 + 4 : MyInt)

@[simp]
theorem MyInt.add_def (x₁ x₂ y₁ y₂ : MyNat)
    : ⟦(x₁, y₁)⟧ + ⟦(x₂, y₂)⟧ = (⟦(x₁ + x₂, y₁ + y₂)⟧ : MyInt) := by
  dsimp [(· + ·), Add.add, MyInt.add, PreInt.add]

-- notation_simp で簡単に展開できるようにする
attribute [notation_simp] PreInt.sr PreInt.r

/-- notation_simp に使用させるための補題 -/
@[notation_simp, simp] theorem MyNat.ofNat_zero : MyNat.ofNat 0 = 0 := rfl
