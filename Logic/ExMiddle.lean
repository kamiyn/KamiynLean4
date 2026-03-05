/-- 二重否定の除去 -/
example (P: Prop) : ¬ ¬ P → P := by
  -- ¬ ¬ P だと仮定する。goal は P
  intro hn2p
  -- 排中律より P ∨ ¬ P が成立する、というタクティク
  by_cases h : P
    -- case pos
    -- すなわち Pが成り立つ場合は即座に証明が終了する
  · exact h
    -- case neg
    -- すなわち Pが成り立たない場合は ¬ ¬ P と矛盾する
  · contradiction

example (P: Prop) : ¬ ¬ P → P := by
  intro hn2p
  by_cases h : P
  · exact h
  -- 上の contradiction の中身の追求
  -- h : ¬P は P → False の略記である
  -- hn2p : ¬¬P は (P → False) → False の略記である
  -- したがって hn2p の引数として h を渡すのが適切
  · exact False.elim (hn2p h)

example (P : Prop) : ¬ ¬ P → P := by
  intro hn2p
  by_cases h : P
  · exact h
  -- absurd の使い方は 今のところわからず
  · exact absurd h hn2p

-- 練習問題
/-- ドモルガンの法則 -/
example (P Q : Prop) : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  -- Goalが ↔ の時は costructor で場合分け
  constructor
  -- case mp ¬ (P ∧ Q) → ¬ P ∨ ¬ Q
  -- Goal が ∨ なら left か right を証明する
  -- 仮定は (P ∧ Q) → False と同値
  · intro hNotPandQ -- ¬ (P ∧ Q) を仮定する
    have hypPNotQ : P → ¬ Q := by
      intro hP
      intro hQ
      have hPandQ : P ∧ Q := by
        constructor
        · exact hP
        · exact hQ
      exact False.elim (hNotPandQ hPandQ)
    -- ここでPに対する排中律を使う
    by_cases hP : P
    · right -- ¬ P ∨ ¬ Q の right である ¬ Q を取り出し
      exact hypPNotQ hP -- P → ¬ Q
    · left -- ¬ P ∨ ¬ Q の left である ¬ P を取り出し
      exact hP

  -- case mpr ¬ P ∨ ¬ Q → ¬ (P ∧ Q)
  · intro hNotPorNotQ -- ¬ P ∨ ¬ Q を仮定する
    intro hPandQ -- P ∧ Q を仮定する
    -- False をGoalとしているので矛盾を証明する
    cases hNotPorNotQ
    case inl hNotP =>
      exact absurd hPandQ.left hNotP -- Not は後ろに置かないといけない
    case inr hNotQ =>
      exact absurd hPandQ.right hNotQ

example (P Q : Prop) : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  constructor
  · intro hNotPandQ
    by_cases hP : P
    · right-- ゴールを ¬ Q に変更
      intro hQ-- hQ : Q, ゴールは False になる
      -- hNotPandQ という関数に、hP と hQ から構成した P ∧ Q の証明を適用し、False を導出する
      -- P ∧ Q は 型レベルであり
      -- ⟨hP, hQ⟩ は項レベル （それぞれ $P$ 型、$Q$ 型を持つ具体的な証明オブジェクト）で実体の構築にあたる
      exact hNotPandQ ⟨hP, hQ⟩
    · left
      exact hP
  · intro hNotPorNotQ
    intro hPandQ
    cases hNotPorNotQ
    case inl hNotP =>
      exact absurd hPandQ.left hNotP
    case inr hNotQ =>
      exact absurd hPandQ.right hNotQ
