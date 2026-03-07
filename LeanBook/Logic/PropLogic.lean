#check Prop

#check (1 + 1 = 3 : Prop)

#check (fun n => n + 3 = 39 : Nat → Prop)

#check True

#check False

/-- True は何も主張していないので、なにもなくても示せる -/
example : True := by trivial -- trivial は自明なことを示すのに使われる タクティク

example (P : Prop) (h : P) : P := by
  exact h
-- (P : Prop) P は命題である という引数
-- (h : P) h は P の証明である という引数 これは 「仮定として Pが成り立っている」というローカルコンテキスト を引数で与えるということ

example (P : Prop) (h : P) : P := by
  assumption
/-- 矛盾からは何でも示せる フェルマーの大定理 -/
example (h : False) : ∀ x y z n : Nat,
    n ≥ 3 → x ^ n + y ^ n = z ^ n → x * y * z = 0 := by
  trivial

-- 含意
example (P Q R : Prop) : (P → Q → R) = (P → (Q → R)) := by
  rfl

#eval True → True
#eval True → False
#eval False → True
#eval False → False
-- 先頭が大文字のTrue/False は命題, 小文字の true/false は真偽値 計算可能かどうかに違いがある

/-- 三段論法 -/
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  -- P → Q が成り立つので、Qを示すには P を示せばよい というように apply の結果 Goal が変わる
  apply h
  -- 仮定 hp : P により証明終わり
  apply hp

/-- 関数適用と同じように h hp で Q を得ることによる証明 -/
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

-- intro タクティク で含意を示す
-- P → Q を示したい場合 P が偽の場合については Q の真偽は問われない
-- なので 「前提 P を仮定として導入してよい」を実現するのが intro
example (P Q : Prop) (hq : Q) : P → Q := by
  -- P → Q を示したいので P であると仮定する
  intro P
  exact hq


#eval ¬ True
#eval ¬ False

-- Pを仮定すると矛盾するから、Pは偽である
-- ¬ P と P → False は**定義上**等しいもの
example (P : Prop) : (¬ P) = (P → False) := by
  rfl

/-- P と ¬ P を同時に仮定すると矛盾する -/
example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  apply hnp
  exact hp

/-- 待遇が元の命題と同値になることの、片方のケース -/
example (P Q : Prop) (h : P → ¬ Q) : Q → ¬ P := by
  -- Q ならば ¬ P を示したいので Qであったと仮定する
  -- intro タクティクは、現在のゴール（示したいこと）の一番外側（左側）にある構造を自動的に解析し、それを前提として取り込む
  -- そのため intro hq と書くだけで hq は Q : Prop に bind される
  intro hq
  -- この時点で ¬ P を示したいのであるが
  -- ¬ P は P → False に等しいので さらに P であったと仮定する
  intro hp
  -- 仮定 h : P → Q → False に適用して False が得られる
  exact h hp hq

-- 仮定に P と ¬ P が両方あるときは明らかに矛盾、矛盾からは何でも示せる
-- そのための専用タクティク contradiction
example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  contradiction

example (P Q : Prop) (hnp : ¬ P) (hp : P) : Q := by
  -- exfalso はゴールを ⊢ False に置き換える
  -- 矛盾からは任意のゴールを示せてしまう
  --「前提における矛盾の発生」を示すことで
  -- 証明の流れを読みやすくする (ゴールを考えることに思考リソースを奪われる無駄を抑制する) 効果がある
  exfalso
  contradiction

#eval True ↔ True
#eval True ↔ False
#eval False ↔ True
#eval False ↔ False

-- 同値性
example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  · apply h1
  · apply h2

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor
  -- 左から右 (Q → P) → P
  case mp =>
    intro h -- h は (Q → P) という仮定を導入する。これを「関数 h」として扱う
    exact h hq -- 関数 h (Q → P) に引数で与えられた (hq : Q) を適用して ゴール P を解決する
  -- 右から左 P → (Q → P)
  case mpr =>
    -- ゴール P → Q → P を順に剥がし、hp : P と hQ : Q を導入する
    -- この hQ は与えられた (hq : Q) **ではない** 未使用変数のため _ アンダースコアにしてもよい
    intro hp hQ
    -- 現在のゴール P に対し、既に持っている hp をそのまま提示する
    exact hp

-- タクティク結合子 <;>
-- 共通導入した変数を長く使い回さず、すぐに解決する場合であれば有用だが
-- 型が異なるケースでは混乱を招くように思われる
example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor <;> intro h
  case mp =>
    -- ここでの h は (Q → P)
    exact h hq
  case mpr =>
    intro hq
    -- ここでの h は P
    exact h

-- rwタクティク 置換
example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  -- P ↔ Q が仮定にあるので Pの代わりにQを示せばよい
  rw [h]
  exact hq

-- 逆向き バックスラッシュL
example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  rw [← h]
  exact hp

example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  rw [h]

#eval True ∧ True
#eval True ∧ False
#eval False ∧ True
#eval False ∧ False

-- constructor タクティクで論理積を示す
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

-- 無名コンストラクタ バックスラッシュ<>
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact ⟨hp, hq⟩

-- 仮定に h : P ∧ Q があるとき、 h.left, h.right により取り出し
example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.left

example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.right

#eval True ∨ True
#eval True ∨ False
#eval False ∨ True
#eval False ∨ False

-- left タクティクを使うことでゴールを ∨ の left 側に変える
example (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

-- left タクティクを使うことでゴールを ∨ の left 側に変える
example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right
  exact hq

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h
  case inl hp =>
    right
    exact hp
  case inr hq =>
    left
    exact hq

-- 練習問題
example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  intro h -- (¬ P ∨ Q) の仮定を導入
  intro hp -- (P → Q) の P の仮定を導入
  cases h
  -- ¬ P の時に (P → Q) を示す
  case inl hnp => -- hnp は ¬ P
    contradiction
  -- Q の時に (P → Q) を示す
  case inr hq => -- hq は Q
    exact hq

example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor
  -- ¬ (P ∨ Q) → ¬ P ∧ ¬ Q を示す
  case mp =>
    intro h -- ¬ (P ∨ Q) を導入する
    constructor -- ¬ P ∧ ¬ Q を分解して示す
    case left => -- ¬ P
      intro hp -- ¬ P は P → False に等しいので P を導入する
      -- この時点では False (矛盾を示したい)
      apply h -- (P ∨ Q) が Goal になる
      left -- P が Goal になる
      exact hp
    case right => -- ¬ Q
      intro hq
      apply h
      right -- Q が Goal になる
      exact hq
  -- ¬ P ∧ ¬ Q → ¬ (P ∨ Q) を示す
  case mpr =>
    intro h -- ¬ P ∧ ¬ Q を仮定する
    intro hORpq -- ¬ (P ∨ Q) は (P ∨ Q) → False に等しいので (P ∨ Q) を導入する
    -- 仮定に ∨ があるときは cases で分岐
    cases hORpq
    case inl hp => -- P
      exact h.left hp -- ¬ P P で False を導く
    case inr hq => -- Q
      exact h.right hq -- ¬ Q Q で False を導く
