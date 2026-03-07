/-- 3重否定の簡略化 -/
example (P : Prop) : ¬ ¬ ¬ P → ¬ P := by
  intro hn3p -- ¬ ¬ ¬ P を仮定し(hn3p)、goal が ¬ P となる
  intro hp -- P を仮定し(hp)、goal が False となる

  -- have タクティク でローカルに補題を示す
  have hn2p : ¬ ¬ P := by
    intro hnp
    -- この時点で hp と hnp が矛盾する
    contradiction

  -- hn3p (¬ (¬ ¬ P)) と hn2p が矛盾する
  contradiction

/-- 3重否定の簡略化  -/
example (P : Prop) : ¬ ¬ ¬ P → ¬ P := by
  intro hn3p hp
  -- have タクティク でローカルに補題を示す
  have hn2p : ¬ ¬ P := by
    intro hnp
    exact False.elim (hnp hp)

  -- show_term を利用して式を変換
  -- False.elim「矛盾が発生したという事実（False）を、現在証明すべき結論（¬ P）へと変換して、証明を完了させる」
  exact False.elim (hn3p hn2p)

example (P : Prop) : ¬ ¬ ¬ P → ¬ P := by
  intro hn3p hp
  have : ¬ ¬ P := by
    intro hnp
    contradiction
  -- this が 無名 have に対する参照として割り当てられる

  -- 【アサーション】 this が期待通りの型 (¬ ¬ P) であることを静的に保証
  -- guard_hyp は証明に直接寄与しない
  guard_hyp this : ¬ ¬ P
  exact False.elim (hn3p this) -- contradiction の対象を明示的に記述

-- 「～を示せば十分である」 ゴールを変更する suffix
example (P : Prop) : ¬ ¬ (P ∨ ¬ P) := by
  -- ¬ (P ∨ ¬ P) と仮定する。この時点で ゴールは Falseになる
  intro h
  -- ここで ¬ P を示せば十分である
  -- 「もし ¬ P が示せれば、現在のゴール（False）が導ける」
  suffices hyp : ¬ P from by
    -- なぜなら ¬ P が成り立つなら P ∨ ¬ P が成り立つため
    have : P ∨ ¬ P := by
      right -- P ∨ ¬ P という have 論理和ゴールの右側を証明する
      exact hyp

    -- this は 直前の have により構築された P ∨ ¬ P
    -- h ¬ (P ∨ ¬ P) と矛盾する
    exact False.elim (h this) -- contradiction

  -- suffices の「from by」が完了し、真の証明目標が ¬ P に更新されたことを確認
  guard_target =ₛ ¬ P

  -- P であると仮定
  intro hp
  -- このとき P ∨ ¬ P が成り立つ
  have : P ∨ ¬ P := by
    left -- P ∨ ¬ P という have 論理和ゴールの左側を証明する
    exact hp

  -- this は 直前の have により構築された (P ∨ ¬ P)
  -- 仮定 h ¬ (P ∨ ¬ P) と矛盾する
  exact False.elim (h this) -- contradiction

-- from by の by を削減するために関数的表記
example (P : Prop) : ¬ ¬ (P ∨ ¬ P) := by
  intro h
  suffices hyp : ¬ P from
    have hnot := Or.inr hyp
    False.elim (h hnot)

  intro hp
  have : P ∨ ¬ P := by
    left
    exact hp
  exact False.elim (h this)

-- exact? タクティク で ライブラリ を検索する
example (P : Prop) : (P → True) ↔ True := by
  exact? -- Try this: exact imp_true_iff P

example (P : Prop) : (True → P) ↔ P := by
  exact? -- Try this: exact true_imp_iff

-- show .. from 構文で一時的な補題を示す
example (P Q : Prop) (h : ¬ P ↔ Q) : (P → False) ↔ Q := by
  rw [show (P → False) ↔ ¬ P from by rfl]
  rw [h]

-- 練習問題
-- 最初に記述した時の解答
example (P : Prop) : ¬ (P ↔ ¬ P) := by
  intro h -- (P ↔ ¬ P) を仮定する

  have hypPpositive : P := by
    rw[h] -- ¬ P を　Goal に置換
    intro hp -- P を仮定
    suffices hyp : ¬ P from by
      contradiction
    rw[← h]
    exact hp

  have hypPnegative : ¬ P := by
    intro hp -- P を仮定
    suffices hyp : ¬ P from by
      contradiction
    rw[← h]
    exact hp

  contradiction

-- Gemini による書き換え案を参照しつつ短縮化を試みる
-- Lean本ではこの時点で rw[h] at hp を解説していないが Gemini が提案してきた
-- …の後 解答ページを見たらほぼ同一の解答に到達しており at を使っていた
-- さらに検討した結果 at を除去してシンプルになった
example (P : Prop) : ¬ (P ↔ ¬ P) := by
  intro h -- (P ↔ ¬ P) を仮定する
  have hypNotP : ¬ P := by
    intro hp
    have hnp : ¬ P := by
      rw [← h]
      exact hp
    exact hnp hp
  -- 初回の解答では2つの独立した補題(ほぼ同型)を作ったが ここでは依存した補題を作ることでコード量を減らす
  have hypP : P := by
    rw[h]
    exact hypNotP

  exact False.elim (hypNotP hypP)
-- Gemini による改善提案
-- 現在のコードは「タクティクによる書き換え」に依存していますが、h は本質的に P → ¬ P という関数を含んでいます。rw でゴールを書き換えるのではなく、**「h.mp（$P$ から $¬ P$ を作る関数）に hp を渡す」**という関数型の発想を持つと、さらに証明が数学的実体に近づきます。
