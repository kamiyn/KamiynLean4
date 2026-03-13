-- 商と Quotient

-- 同値類 equivalence class
section
  variable {α : Type} (sr : Setoid α)
  -- 「『sr : Setoid α による同値類』を求める操作」 が Quotient.mk sr
  #check (Quotient.mk sr : α → Quotient sr)
end

-- 型 α は (Quotient.mk sr で導かれる) 同値類 たちの直和
-- 同値類の全体 が α上の同値関係sr : Setoid αによる商 Quotient sr
-- Quotient.mk sr は 商 Quotient sr への関数 で 自然な関数 (canonical projection)

-- 代表元 representative を取る
section
  variable {α : Type} (sr : Setoid α)

  -- ⊢ True は常に成功する (trivial で証明完了する)
  -- 以下のコード片は Quotient.inductionOn から x : α を得たことを記述したもの
  example (a : Quotient sr) : True := by
    induction a using Quotient.inductionOn with
    | h x =>
      guard_hyp x : α
      trivial
end

section
  variable {α β : Type} (sr : Setoid α)
  variable (f : β → α)

  -- 自然な写像 α → Quotient sr と f を合成することで 商への関数が得られる
  #check (Quotient.mk sr ∘ f : β → Quotient sr)
  -- ⊢ β → Quotient sr
end

section
  variable {α β : Type} (sr : Setoid α)
  variable (f : α → β) (h : ∀ x y, x ≈ y → f x = f y)
  #check (Quotient.lift f h : Quotient sr → β)
end

section
  /- ## Quotient.lift は元の関数の値を変えない -/
  variable {α β : Type} (sr : Setoid α)
  variable (f : α → β) (h : ∀ x y, x ≈ y → f x = f y)
  example : ∀ x, (Quotient.lift f h) (Quotient.mk sr x) = f x := by
    intro x
    rfl
end

-- α上の同値関係sr : Setoid αによる商 Quotient sr を
-- α/sr := Quotient sr と表記する
section
  /- ## 同値なら商へ送って等しい Quotient.sound という名前がついている -/
  variable {α : Type} (sr : Setoid α)
  -- h : x ≈ y とする
  variable (x y : α) (h : x ≈ y)

  -- このとき 自然な写像 α → α/sr による像が等しくなっている
  -- これを「商に送って等しい」と表現する
  example : Quotient.mk sr x = Quotient.mk sr y := by
    apply Quotient.sound
    exact h
end

section
  /- ## 商に送って等しいなら同値 Quotient.exact という名前がついている -/
  variable {α : Type} (sr : Setoid α)
  variable (x y : α)
  example (h : Quotient.mk sr x = Quotient.mk sr y) : x ≈ y := by
    exact Quotient.exact h
end

-- 練習問題
/-- β 上の二項関係 r : β → β → Prop と関数 f : α → β があるとき、α 上の二項関係を fun x y => r (f x) (f y) で定義できる -/
private def Rel.comap {α β : Type} (f : α → β) (r : β → β → Prop)
  : α → α → Prop :=
  fun x y => r (f x) (f y)

/-- β 上の同値関係 sr : Setoid β と関数 f : α → β があるとき、Rel.comap f (· ≈ ·) も同値関係になる -/
private def Setoid.comp {α β : Type} (f : α → β) (sr : Setoid β)
    : Setoid α where
  r := Rel.comap f (· ≈ ·)
  iseqv := by -- ⊢ Equivalence (Rel.comap f fun x1 x2 => x1 ≈ x2)
    constructor
    case refl =>
      intro x -- Rel.comap f (fun x1 x2 => x1 ≈ x2) x x
      -- dsimp [Rel.comap] refl に関しては 実施しなくていい
      exact Setoid.refl (f x)
      -- 当初以下のように書いたが Setoid.refl に引数を渡すことで解決できることがわかった
      -- 定義に立ち戻れ、という教訓を示しているように思える

      -- dsimp [Rel.comap] -- ⊢ f x ≈ f x
      -- have : ∃ y : β, f x = y := by
      --   simp
      -- obtain ⟨k, hk⟩ := this
      -- rw [hk]
      -- exact Setoid.refl k
    case symm =>
      intro x y h -- Rel.comap f (fun x1 x2 => x1 ≈ x2) x y → Rel.comap f (fun x1 x2 => x1 ≈ x2) y x
      -- h : Rel.comap f (fun x1 x2 => x1 ≈ x2) x y
      -- ⊢ Rel.comap f (fun x1 x2 => x1 ≈ x2) y x
      dsimp [Rel.comap] at *
      -- h : f x ≈ f y
      -- ⊢ f x ≈ f y
      exact Setoid.symm h
    case trans =>
      intro x y z hxy hyz
      -- hxy : Rel.comap f (fun x1 x2 => x1 ≈ x2) x y
      -- hyz : Rel.comap f (fun x1 x2 => x1 ≈ x2) y z
      -- ⊢ Rel.comap f (fun x1 x2 => x1 ≈ x2) x z
      dsimp [Rel.comap] at *
      -- hxy : f x ≈ f y
      -- hyz : f y ≈ f z
      -- ⊢ f x ≈ f z
      exact Setoid.trans hxy hyz

private def Setoid.comp2 {α β : Type} (f : α → β) (sr : Setoid β)
    : Setoid α where
  r := Rel.comap f (· ≈ ·)
  iseqv := by
    constructor <;> dsimp [Rel.comap] -- 共通で dsimp を適用
    case refl =>
      intro x
      apply Setoid.refl -- apply で書くと (f x) を書かなくても完了する
    case symm =>
      intro x y
      exact Setoid.symm
    case trans =>
      intro x y z
      exact Setoid.trans
