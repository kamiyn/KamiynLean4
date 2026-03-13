-- Lean 依存型
-- 一般的なプログラミング言語では f a の型は固定だが、Lean では a に依存することができる

#check Nat.add_zero
#check Nat.add_zero 0
#check Nat.add_zero 42

-- Nat.add_zero は Nat 上の関数であり
-- 任意の入力 n : Nat に対して n + 0 = n の 証明項 を返す
#check (Nat.add_zero : (n : Nat) → n + 0 = n)

-- 返り値の型が入力の値に依存して変わる関数 「依存関数」dependent function その型を 「依存関数型」(または Π型) と呼ぶ
-- Lean では 全称量化 ∀ は依存関数型の別表記であり、まったく同じ
-- Lean InfoView 上でもまったく同じであることが確認できる
example : (∀ n : Nat, n + 0 = n) = ((n : Nat) → n + 0 = n) := by
  rfl

-- ∀ を 依存関数型として表示させる
set_option pp.foralls false in
#check (∀ n : Nat, n + 0 = n)

-- 標準ライブラリにおける List の定義
-- inductive List (α : Type) : Type where
--   | nil
--   | cons (a : α) (l : List α)

-- List α は要素数の情報を持たない
example : List Nat := [0, 1, 2, 3]
example : List Nat := [0, 1]

inductive Vect (α : Type) : Nat → Type where
  -- 空ベクトルは 長さ 0 のベクトル
  | nil : Vect α 0
  -- ベクトル v : Vect α n の先頭に a : α を追加することで新しいベクトルが得られる
  | cons {n : Nat} (a : α) (v : Vect α n) : Vect α (n + 1)
-- Vect Nat 0 と Vect Nat 1 は別々の型
example : Vect Nat 0 := Vect.nil
example : Vect Nat 1 := Vect.cons 42 Vect.nil

-- 依存ペア (Σ 型とも呼ばれる)
example : (α : Type) × α := ⟨Nat, 1⟩
example : (α : Type) × α := ⟨Bool, true⟩
example : (α : Type) × α := ⟨Prop, True⟩
-- https://github.com/LambdaNote/errata-leanbook-1-1/issues/59
-- 地の文 7 行目は \<> を使わず Parentheses でリスト要素を記述しているが
-- 「各要素 (x, y)」という書き方もしているので Lean文法 ではなく LISP に近い表記を採用しているのかもしれない

example : List ((α : Type) × α) := [⟨Nat, 1⟩, ⟨Bool, true⟩, ⟨Prop, True⟩]

-- 練習問題
-- 解答がないのは 生成プログラム上の不具合らしい https://github.com/LambdaNote/errata-leanbook-1-1/issues/59
example : List ((α : Type) × α) := [⟨Nat, 42⟩, ⟨Bool, false⟩]

-- intro を使った解法
example : {α : Type} → {n : Nat} → (a : α) → (v : Vect α n) → Vect α (n + 1) := by
  intro α n
  -- 1. 追加する要素 a : α を導入。
  intro ha
  -- 2. 既存のベクトル v : Vect α n を導入。この型は Nat に依存している。
  intro vectAlphaN
  -- 3. Vect のコンストラクタである cons を適用。
  --    第1引数に要素、第2引数に既存のベクトルを取ることで、型レベルの長さが自動的に n + 1 に更新される。
  exact Vect.cons ha vectAlphaN

-- fun a v を使えば1行
example : {α : Type} → {n : Nat} → (a : α) → (v : Vect α n) → Vect α (n + 1) :=
  fun a v => Vect.cons a v

-- 型を明示的に記述する
example : {α : Type} → {n : Nat} → (a : α) → (v : Vect α n) → Vect α (n + 1) :=
  fun {α : Type} {n : Nat} (a : α) (v : Vect α n) => Vect.cons a v
