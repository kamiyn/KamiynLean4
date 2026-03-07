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
  -- P' = P, Q' = ¬ ¬ P と置くと、contra_equiv は以下のように特殊化できる：
  -- (¬ P → ¬ ¬ ¬ P) ↔ (¬ ¬ P → P)
  -- 1. 全称化された関数 contra_equiv に P と ¬¬P を適用し、
  --    得られた Iff 構造体を分解して順方向の含意を取り出す
  -- Note: ∀ に対して obtain を使うのは、正確には「∀ の結果が ∧ や ↔ などの構造を返す場合」に限られます。
  --    ∃ に対する obtain とは 操作の性質 が根本的に異なり 練習問題時点では解説されていない
  obtain ⟨h_forward, _⟩ := contra_equiv P (¬ ¬ P)
  -- 2. 結論 (Q' → P') をゴール (¬ ¬ P → P) に一致させ、証明すべき内容を前件 (¬P → ¬Q') へと帰着させる逆向きの推論
  --    ここで h_forward は (¬P → ¬¬¬P) → (¬¬P → P)
  apply h_forward
  -- 3. 新しいゴール (¬ P → ¬ ¬ ¬ P) の証明
  --    ゴール ¬P → ¬¬¬P に対して、前提として hnp と hnnp を導入する
  --    このとき、ゴールは False となる（否定の定義 Not P := P → False による）
  intro hnp hnnp
  -- 4. hnnp : (¬ ¬ P) に hnp : (¬ P) を適用して、直接 False を導く
  --    より厳密には 高階関数 hnnp : (P → False) → False に対して、引数 hnp : P → False を適用
  exact hnnp hnp
  -- Note: False.elim（$\text{ex falso quodlibet}$）は、「矛盾から任意の命題を導く」ために使われますが、ゴールそのものが False である場合は、単に exact hnnp hnp と記述するのが、最も直接的でノイズの少ない証明

-- 'double_negation_or_contra_equiv_obtain' does not depend on any axioms
-- obtain を使った記述は公理依存ゼロ
#print axioms double_negation_or_contra_equiv_obtain


-- Geminiは このようにも書けると出してきたが カリー・ハワード同型対応 は次の話題
theorem double_negation_or_contra_equiv_term (P : Prop)
  (contra_equiv : ∀ (P' Q' : Prop), (¬ P' → ¬ Q') ↔ (Q' → P')) : ¬ ¬ P → P :=
  (contra_equiv P (¬ ¬ P)).mp (fun (hnp : ¬ P) (hnnp : ¬ ¬ P) => hnnp hnp)

-- https://github.com/LambdaNote/errata-leanbook-1-1/issues/52
-- 差し替え予定の練習問題
/-- 「二重否定の除去」の二重否定 ただし 排中律を使ってはいけません -/
theorem double_negation_elim' (P : Prop) : ¬¬ (¬¬ P → P) := by
  intro h1 -- ¬ (¬¬ P → P)
  apply h1
  intro h2 -- ¬¬ P
  exfalso -- ここで Goal を矛盾に変更する
  apply h2 -- Goal は ¬ P
  intro hp -- ここで P が仮定された!
  apply h1 -- 再度 ¬¬ P → P が Goalになる
  intro _
  exact hp

-- Classical.choiceに依存していないことを確認してください
#print axioms double_negation_elim'
