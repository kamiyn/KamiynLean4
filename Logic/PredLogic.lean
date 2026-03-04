/-- 恒等関係を定義した述語 -/
def P (n : Nat) : Prop := n = n

-- 次の行の P a の P は def P で定義されたもの
example : ∀ a : Nat, P a := by
  -- 全称化された項 a を、任意の値 x としてコンテキストに導入（Bind）する
  intro x
  -- dsimp は 「定義への展開」を実行できるタクティク
  -- 述語 P の定義を展開し、ゴールを x = x に簡約（Reduction）する
  -- Lean 4 の dsimp は、展開した結果が x = x のような 「自明な等式」になった場合、自動的に rfl を試みてゴールを閉じます。
  dsimp [P]

example : ∀ a : Nat, P a := by
  intro x -- 任意に与えられた a を x という名前で受け取り、ゴールを P x に変化させる
  unfold P -- 述語 P の定義を展開（Unfold）し、ゴールを具体的な x = x の形にする
  rfl -- 反射律（Reflexivity）により、定義上等しい両辺を一致させて証明を完了する

-- カーネルの型チェックにおいて δ-簡約が暗黙的に行われるため、明示的な unfold は省略可能
example : ∀ a : Nat, P a := by
  -- a : Nat を x という名前でローカルコンテキストに導入（Bind）し、ターゲットを P x とする
  intro x
  -- 反射律（Reflexivity）により、P x が定義上 x = x と等価であることを検証し証明を完了する
  rfl

/-- すべての自然数 x について P x が成り立つなら、 P 0 も成り立つ -/
example (P : Nat → Prop) (h : ∀ x : Nat, P x) : P 0 := by
  -- h を 0に適用すれば明らか
  exact h 0

/-- 偶数であることを表す術語 -/
def even (n: Nat) : Prop := ∃ m : Nat, n = m + m

/-- 4 :Nat は偶数 -/
example : even 4 := by
  -- この証明のために exists タクティクを使う
  exists 2

example (α : Type) (P Q : α → Prop) (h : ∃ x : α, P x ∧ Q x)
    : ∃ x : α, Q x := by
  -- 仮定 h が存在を主張しているy を取り出す
  obtain ⟨y, hy⟩ := h
  -- この y が求めるものである
  exists y
  -- なぜなら、P y ∧ Q y が成り立つから その right である Q y を取り出す
  exact hy.right

-- opaque は実装を与えずに存在だけ宣言する文法
/-- 人間たちの集合 -/
opaque Human : Type
/-- 愛の関係 Love x y が成り立つとき x は y を愛している とする -/
-- 専用の中置記法を用意する 50は演算子のパース優先順位を表す 優先順位が高いものが先に適用される
opaque Love : Human → Human → Prop
@[inherit_doc] infix:50 " -♥→ " => Love

/-- すべての人に愛されているアイドルが存在する -/
-- 量化子 の順番は重要
-- 量化子のスコープは右側に最大まで伸びる（Greedy Scope）ため、
-- 以下の idolExists と idolExists_explicit は構文的に等価である。
def IdolExists : Prop := ∃ idol : Human, ∀ h : Human, h -♥→ idol
-- カッコを用いてスコープを明示した版。
def idolExists_explicit : Prop := ∃ idol : Human, (∀ h : Human, h -♥→ idol)

/-- 誰にでも好きな人の1人くらいいる -/
def EveryoneLovesSomeone : Prop := ∀ h : Human, ∃ tgt : Human, h -♥→ tgt
def EveryoneLovesSomeone_explicit : Prop := ∀ h : Human, (∃ tgt : Human, h -♥→ tgt)

-- #check ∃ philan : Human, ∀ h : Human, philan -♥→ h
def PhilanExists : Prop := ∃ philan : Human, ∀ h : Human, philan -♥→ h

def EveryoneLoved : Prop := ∀ h : Human, ∃ lover : Human, lover -♥→ h

example : PhilanExists → EveryoneLoved := by
  -- 博愛主義者の存在を仮定する
  intro h
  -- 存在が主張されている博愛主義者を philan とする
  -- このとき定義から h : ∀ human : Human, philan -♥→ human が成り立つ
  obtain ⟨philan, hypPhilan⟩ := h
  -- このとき EveryoneLoved を示したい
  -- 定義より、∀ h : Human, ∃ lover : Human, lover -♥→ h を示せばよい
  dsimp[EveryoneLoved]
  -- 任意に human : Human が与えられたと仮定する。Goal は ∃ lover : Human, lover -♥→ h
  intro humanAssumed
  -- Goalの lover = philan とする
  exists philan
  -- この時点で Goal が philan -♥→ humanAssumed になる
  -- hypPhilan : ∀ human : Human, philan -♥→ human なので humanAssumed を渡して証明完了
  exact hypPhilan humanAssumed

-- 練習問題
example : IdolExists → EveryoneLovesSomeone := by
  -- アイドルの存在を仮定する
  intro hIdol
  obtain ⟨idol, hypIdol⟩ := hIdol
  dsimp[EveryoneLovesSomeone]
  -- ∀ h : Human, ∃ tgt : Human, h -♥→ tgt が Goal
  intro humanAssumed
  -- Goal は ∃ tgt : Human, humanAssumed -♥→ tgt
  exists idol
  -- この時点で Goal が humanAssumed -♥→ idol になる
  -- hypIdol が ∀ h : Human, h -♥→ idol なので humanAssumed を渡して証明完了
  exact hypIdol humanAssumed
-- 本の解答は dsimp を先に行うことで intro 行を1行に短縮している
