-- 同値関係 Equivalence
-- 二項関係 r が同値関係である とは以下を満たす
-- 反射律 : ∀ a : α, r a a
-- 対称律 : ∀ a b : α, r a b → r b a
-- 推移律 : ∀ a b c : α, r a b → r b c → r a c

/-- 2次元平面 -/
structure Point where
  x : Int
  y : Int

#check { x := 1, y := 2 : Point}
#check Point.mk -- コンストラクタ Point.mk (x y : Int) : Point
#check Point.mk 1 2

#check Point.x -- アクセサ Point.x (self : Point) : Int
#check Point.y -- アクセサ Point.y (self : Point) : Int

#eval
  let p : Point := { x := 1, y := 2 }
  p.x

/-- 同値関係 -/
-- 標準ライブラリにおける Equivalence の定義
-- structure Equivalence {α : Sort u} (r : α → α → Prop) : Prop where
--   /-- r は反射的 : x ~ x -/
--   refl : ∀ x, r x x
--   /-- r は対称的 : x ~ y → y ~ x -/
--   symm : ∀ {x y}, r x y → r y x
--   /-- r は推移的 : x ~ y かつ y ~ z ならば x ~ z -/
--   trans : ∀ {x y z}, r x y → r y z → r x z

-- h の同値性 から 反射的 であることを導く (Equivalence の定義を使う)
example {α : Type} (r : α → α → Prop) (h : Equivalence r) : ∀ x, r x x := by
  exact h.refl

-- 以下のように枠組みを書いてから間を埋める
-- example {α : Type} : Equivalence (fun x y : α => x = y) := by
--   constructor
--   case refl =>
--     sorry
--   case symm =>
--     sorry
--   case trans =>
--     sorry

example {α : Type} : Equivalence (fun x y : α => x = y) := by
  constructor -- Equivalence という構造体を分解する
  case refl => -- 反射律 ⊢ ∀ (x : α), x = x
    intro x -- x = x
    rfl
  case symm => -- 対称律 ⊢ ∀ {x y : α}, x = y → y = x
    intro x y h -- h : x = y, ⊢ y = x
    rw [h]
  case trans => -- 推移律 ⊢ ∀ {x y z : α}, x = y → y = z → x = z
    intro x y z hxy hyz
    -- hxy : x = y
    -- hyz : y = z
    -- ⊢ x = z
    rw [hxy, hyz]

-- 同値関係は Setoid α という型クラスで表現する
-- α 上の二項関係 r と 同値関係であるという証明 iseqv : Equivalence r をまとめたもの
-- 標準ライブラリにおける Setoid 型クラスの定義
-- class Setoid (α : Sort u) where
--   /-- 二項関係 r : α → α → Prop -/
--   r : α → α → Prop
--   /-- 二項関係 r は同値関係である -/
--   iseqv : Equivalence r

-- sr : Setoid α があるとき 二項関係(同値関係) sr.r を ≈ という記号で表せる
example {α : Type} (sr : Setoid α) (x y : α) : sr.r x y = (x ≈ y) := by
  rfl

-- 練習問題
example {α : Type} : Equivalence (fun _x _y : α => true) := by
  constructor
  case refl => -- ⊢ ∀ (x : α), true = true
    intro x -- ⊢ true = true
    rfl -- 本だと trivial
  case symm => -- ⊢ ∀ {x y : α}, true = true → true = true
    intro x y h -- ⊢ true = true
    rfl
  case trans =>
    intro x y z hxy hyz -- ⊢ true = true
    rfl
