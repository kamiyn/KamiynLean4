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
  · intro h -- ¬ (P ∧ Q) を仮定する
    have hypPQ : P → ¬ Q := by
      intro hP
      intro hQ
      have hPandQ : P ∧ Q := by
        constructor
        · exact hP
        · exact hQ
      exact False.elim (h hPandQ)

    have hypQP : Q → ¬ P := by
      intro hQ
      intro hP
      have hPandQ : P ∧ Q := by
        constructor
        · exact hP
        · exact hQ
      exact False.elim (h hPandQ)



  -- case mpr ¬ P ∨ ¬ Q → ¬ (P ∧ Q)
  · intro hNotPorNotQ -- ¬ P ∨ ¬ Q を仮定する
    intro hPandQ -- P ∧ Q を仮定する
    -- False をGoalとしているので矛盾を証明する
    cases hNotPorNotQ
    case inl hNotP =>
      exact absurd hPandQ.left hNotP -- Not は後ろに置かないといけない
    case inr hNotQ =>
      exact absurd hPandQ.right hNotQ
