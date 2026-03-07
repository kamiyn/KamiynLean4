-- 排中律は Lean では Classical.em という名前で定義されている
-- このうち .em の部分が Law of excluded middle の頭文字を表している
#check Classical.em
-- 依存する公理を出力する
#print axioms Classical.em

#check Classical.choice

/-- 関数の全射性 -/
def Surjective { X Y : Type } (f : X → Y) : Prop :=
  ∀ y : Y, ∃ x : X, f x = y
example : Surjective (fun x : Nat => x) := by
  intro y
  exists y

-- (X Y : Type) で宣言すると型が一致しない
-- def SurjectiveBroken (X Y : Type) (f : X → Y) : Prop :=
--   ∀ y : Y, ∃ x : X, f x = y
-- example : SurjectiveBroken (fun x : Nat => x) := by
--   intro y
--   exists y

-- Application type mismatch: In the application
--   SurjectiveBroken fun x => x
-- the argument
--   fun x => x
-- has type
--   Nat → Nat : Type
-- but is expected to have type
--   Type : Type 1

variable {X Y : Type}

-- noncomputable は「計算できない」ことを表す。これは Classical.choice の利用からくる要請
noncomputable def inverse (f : X → Y) (hf : Surjective f) : Y → X := by
  -- Y → X より y : Y が与えられたとする
  intro y
  -- f は全射なので {x // f x = y} は空でない
  -- {x // f x = y} は部分型 subtype を表す。ここでは f x = y が成り立つ x という型
  have : Nonempty {x // f x = y} := by
    -- Surjective ∀ y : Y, ∃ x : X, f x = y を適用した結果より
    -- let を利用して **証拠（Witness）とその性質の証明（Proof）**を同時に取り出し、ローカルな文脈に導入
    let ⟨x, hx⟩ := hf y
    -- 外側の ⟨ ⟩ は Nonempty.intro
    -- 内側の ⟨ ⟩ は Subtype.mk (引数は値 x と証明 hx) を表す
    -- exact ⟨⟨x, hx⟩⟩
    exact Nonempty.intro ⟨x, hx⟩
--    exact Nonempty.intro (⟨x, hx⟩ : {x // f x = y})
  -- 選択原理を用いて、f x = y なる x : X を構成する
  have x := Classical.choice this
  exact x.val

/-- 対偶が元の命題と同値であることを認めれば、二重否定の除去が導ける -/
-- この練習で **排中律を使ってはいけません**
theorem double_negation_or_contra_equiv (P : Prop)
  (contra_equiv : ∀ (P Q : Prop), (¬ P → ¬ Q) ↔ (Q → P)) : ¬ ¬ P → P := by
  rw[← contra_equiv]
  -- ¬P → ¬¬¬P に変換
  intro hnp
  intro hnnp
  exact False.elim (hnnp hnp) -- ¬ は P → False と定義上等しいので Not側を先に書いて適用する必要がある

-- Classical.choice に依存していないことを確認してください
#print axioms double_negation_or_contra_equiv

-- rw[h] を使わないよう Gemini の支援を得て書き換え
theorem double_negation_or_contra_equiv_norw (P : Prop)
  (contra_equiv : ∀ (P' Q' : Prop), (¬ P' → ¬ Q') ↔ (Q' → P')) : ¬ ¬ P → P := by
  -- ゴール ¬ ¬ P → P は、(Q' → P') の形をしている。
  -- ここで P' = P, Q' = ¬ ¬ P と置くと、contra_equiv は以下のようになる：
  -- (¬ P → ¬ ¬ ¬ P) ↔ (¬ ¬ P → P)
  -- これを算出するのが contra_equiv P (¬ ¬ P)

  -- (¬ P → ¬ ¬ ¬ P) → (¬ ¬ P → P) を適用し
  -- 左側の命題 (¬ P → ¬ ¬ ¬ P) の証明へと帰着させる。
  apply (contra_equiv P (¬ ¬ P)).mp

  -- 現在のゴール: ¬ P → ¬ ¬ ¬ P
  intro hnp    -- ¬ P
  intro hnnp  -- ¬ ¬ ¬ P (これは ¬ ¬ P → False と同値)
  -- ¬ ¬ P を作れば False が導ける
  -- hnnp は (¬ P → False) → False のような構造
  exact hnnp hnp

-- obtain を使って書く
theorem double_negation_or_contra_equiv_obtain (P : Prop)
  (contra_equiv : ∀ (P' Q' : Prop), (¬ P' → ¬ Q') ↔ (Q' → P')) : ¬ ¬ P → P := by
  -- 1. ∀ に具体的な命題 P と ¬¬P を適用し、得られた ↔ を分解する
  obtain ⟨h_forward, h_backward⟩ := contra_equiv P (¬ ¬ P)

  -- 2. ゴール ¬¬P → P を達成するために、(¬P → ¬¬¬P) → (¬¬P → P) の向き (h_forward) を使う
  apply h_forward

  -- 3. 新しいゴール: ¬P → ¬¬¬P
  intro hnp    -- ¬P
  intro hnnp   -- ¬¬P
  -- hnnp : (P → False) → False, hnp : P → False なので、hnnp hnp は False
  exact hnnp hnp
